module

public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.SheafificationOfTheCohomologyPresheaf
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MonoHomologyProjection

/-!
# Injectivity of cohomology of a derived limit over an object of a ringed site

Let `(C, O)` be a ringed site and let `(K_n)` be an inverse system in `D(O)` with derived limit
`L`, presented by its defining distinguished triangle.  Fix an object `U` of the site, a degree
`m` and an index `N`.  If the transition maps of the system become isomorphisms beyond `N` on
cohomology over `U` in the two degrees `m - 1` and `m`, then

```
Hᵐ(U, L) ⟶ Hᵐ(U, K_N)
```

is injective.  This is the cohomology-over-an-object half of Stacks 0D6L.

## Main results

* `derivedSectionsPresheaf_isTriangulated`: derived sections of a ringed site, as a derived
  presheaf, is a triangulated functor.
* `mono_cohomologyPresheaf_projection_of_eventually_iso`: the injectivity statement above.

## Implementation notes

The engine is `mono_homology_projection_of_eventually_iso`, which takes an arbitrary
triangulated functor to a derived category followed by a homology functor and an exact functor
to abelian groups.  Here that functor is `derivedSectionsPresheaf` of Stacks 0BKV and the exact
functor is evaluation at `U` composed with the forgetful functor to abelian groups, so the
composite is the cohomology `Hᵐ(U, -)` of Stacks 0BKV's `cohomologyPresheaf`.

Triangulatedness of `derivedSectionsPresheaf` is the one piece that had to be supplied.  It is
`Stacks.Injectives.rightDerivedFunctor_isTriangulated` instantiated at the forgetful functor
from sheaves of modules to presheaves of modules, which is additive, out of a Grothendieck
abelian category.  That lemma needs none of the exactness-of-countable-products hypotheses of
its file, which it `omit`s.

**This file does not prove Stacks 0D6L.**  Stacks 0D6L assumes only that `R¹lim Hᵐ⁻¹(V_i, K_n)`
vanishes and that `Hᵐ(V_i, K_n) ⟶ Hᵐ(V_i, K_{n(V)})` is injective, over a cofinal system of
coverings of `V`, and concludes injectivity on sections of the cohomology *sheaf* at `V`.  The
statement proved here instead assumes the transition maps are *isomorphisms* beyond `N`, which
is strictly stronger, and concludes over a single object rather than on sheaf sections.  It is
therefore not tagged.  It is, however, exactly the form in which Stacks 0D6M invokes 0D6L: the
Claim in 0D6M's proof supplies isomorphisms in both degrees.

**Universe narrowing.**  `RingedSite.{u, u, u}` collapses the site, morphism and ring universes.
This is inherited from the already-tagged Stacks 0BKV chain, whose five tagged clauses are
all stated at `RingedSite.{u, u, u}`, and is not decided here.

## References

* [Stacks Project, Tag 0D6L](https://stacks.math.columbia.edu/tag/0D6L)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Cohomology.SiteCohomologyPresheaf

universe u

namespace Stacks.Cohomology.DerivedLimitSectionsInjectivity

attribute [local instance] HasDerivedCategory.standard

variable (X : RingedSite.{u, u, u})

/-- **Derived sections of a ringed site is a triangulated functor.**  The forgetful functor from
sheaves of modules to presheaves of modules is additive and its source is Grothendieck abelian,
so every object of the derived category is represented by a K-injective complex, where the unit
of the derived functor is an isomorphism.

The unit is written out rather than abbreviated: a `def` wrapping it hides the
`IsRightDerivedFunctor` instance that the criterion needs. -/
public instance derivedSectionsPresheaf_isTriangulated :
    (derivedSectionsPresheaf X).IsTriangulated :=
  letI : (SheafOfModules.forget.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).Additive :=
    SheafOfModules.instAdditivePresheafOfModulesObjFunctorOppositeRingCatIsSheafForget
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  Stacks.Injectives.rightDerivedFunctor_isTriangulated
    (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (derivedSectionsPresheaf X)
    ((homotopySectionsPresheaf X).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ)))

/-- **Injectivity of cohomology of a derived limit over an object (Stacks 0D6L, over a single
object, with isomorphic transition maps).**  Let `L` be a derived limit of the inverse system
`K`, presented by its defining distinguished triangle.  If the transition maps of `K` beyond
`N` become isomorphisms on cohomology over `U` in degrees `m - 1` and `m`, then
`Hᵐ(U, L) ⟶ Hᵐ(U, K_N)` is injective. -/
public theorem mono_cohomologyPresheaf_projection_of_eventually_iso
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    {L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧)
    (hT : Triangle.mk p (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
          K.map (homOfLE (Nat.le_succ n)).op) δ ∈
      distTriang
        (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (U : X.C) (m : ℤ) (N : ℕ)
    (hpres : ∀ r : ℤ, m - 1 ≤ r → r ≤ m →
      PreservesLimit (Discrete.functor (fun n : ℕ ↦ K.obj ⟨n⟩))
        (derivedSectionsPresheaf X ⋙
          DerivedCategory.homologyFunctor
            (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) r ⋙
          presheafSections X U))
    (hiso : ∀ r : ℤ, m - 1 ≤ r → r ≤ m → ∀ n : ℕ, N ≤ n →
      IsIso ((derivedSectionsPresheaf X ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) r ⋙
        presheafSections X U).map (K.map (homOfLE (Nat.le_succ n)).op))) :
    Mono ((derivedSectionsPresheaf X ⋙
      DerivedCategory.homologyFunctor
        (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) m ⋙
      presheafSections X U).map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) N)) :=
  mono_homology_projection_of_eventually_iso
    (derivedSectionsPresheaf X) (presheafSections X U) K p δ hT m N hpres hiso

end Stacks.Cohomology.DerivedLimitSectionsInjectivity

end
