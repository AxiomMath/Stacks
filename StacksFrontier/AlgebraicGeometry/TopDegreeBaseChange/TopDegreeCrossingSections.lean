module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.EdgeCompatSectionsOverOpen
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.TopDegreeCrossingSingleModel

/-!
# The `γ⁺` side's leading crossing, read under sections over an open

The tail of conclusion (c) of [Stacks, Tag 0EX3] begins with
`…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso` inverted — the crossing of the two
models of `Rf'_*` that the `γ⁺` side is built on — and everything after it is read under sections
over an affine open `V` of the base. This file supplies the one identity that gets that factor
into the model of derived sections over an open: the edge morphism of `RΓ(V, -)` followed by
`Γ(V, -)` of that crossing is a composite of the collapse factor of [Stacks, Tag 01XK] and the
comparison of the two indexings of the right derived functors.

Nothing new is proved. `Stacks.EdgeCompat`
`.singleCompDerivedSections_hom_app_comp_rightDerivedCompNatIso_inv` is the collapse mirror of
[Stacks, Tag 01XK] at the pair `(f_*, Γ(V, -))`, and it already exhibits the edge morphism of
`RΓ(V, -)` followed by `Γ(V, -)` of the **single-complex** crossing
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`. The two crossings differ by
a factor of `Stacks.DerivedIndexing.rightDerivedIso`, by
`…TopDegreeBaseChange.singleCompDerivedCompHomologyIsoRightDerived_hom_app_eq`, and that factor
is one the `ψ` side's tail already carries. So the content here is the bookkeeping that moves it
across, and the only inverse asked for is the Leray one, which is unconditional.

## Main results

* `…TopDegreeBaseChange.sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerived`
  `PushforwardIso_hom_eq`: **the edge morphism of `RΓ(V, -)` at `Rf_*((E Z)[0])`, followed by
  `Γ(V, -)` of the `γ⁺` side's crossing, is the collapse factor of [Stacks, Tag 01XK] and the
  comparison of the two indexings.** No hypothesis on `f`, on `V` or on the object beyond the
  pointwise homology-preservation hypothesis Grothendieck's comparison itself carries and a left
  inverse of the Leray comparison's degree-`n` cohomology.

The composite the left-hand side names is exactly the prefix the tail chase needs: postcomposing
it with `Γ(V, -)` of the crossing **inverted** — which is where the `γ⁺` side's tail starts —
leaves the edge morphism of `RΓ(V, -)` alone, and that is the factor the naturality of the edge
morphism carries along the rest of the tail.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open DerivedCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.HypercohomologyEdge.HomologyComparison (derivedHomologyComparison)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] RingedSpaceModuleAdjunction.preservesLimits_modulePushforward
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (n : ℕ)
  {Dc : Type*} [Category* Dc]
  (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))

/-- **A leading left inverse and a trailing cancelling pair, moved across a functor.** From
`m = a ≫ e ≫ G(u ≫ w)` together with a left inverse `a'` of `a` and a right inverse `w'` of `w`
one gets `e ≫ G u = a' ≫ m ≫ G w'`. Stated at variables of abstract categories, where every
reassociation is free and the functor is applied to variables only: at the application the
unifier meets the concrete crossings in argument position and never has to re-elaborate a
composite spanning the `AlgebraicGeometry.Scheme.Modules` divide. -/
private theorem comp_map_eq {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {P Q : D} {A A' B : C}
    {a : P ⟶ Q} {a' : Q ⟶ P} (ha : a' ≫ a = 𝟙 Q)
    {e : Q ⟶ G.obj A} {u : A ⟶ A'} {w : A' ⟶ B} {w' : B ⟶ A'} (hw : w ≫ w' = 𝟙 A')
    {m : P ⟶ G.obj B} (hm : m = a ≫ e ≫ G.map (u ≫ w)) :
    e ≫ G.map u = a' ≫ m ≫ G.map w' := by
  have key : a' ≫ m ≫ G.map w' = (a' ≫ a) ≫ e ≫ G.map (u ≫ w) ≫ G.map w' := by
    rw [hm]; simp only [Category.assoc]
  rw [key, ha, Category.id_comp, ← G.map_comp, Category.assoc, hw, Category.comp_id]

/-- **The edge morphism of `RΓ(V, -)` followed by `Γ(V, -)` of the `γ⁺` side's crossing of the two
models of `Rf_*`.** For a morphism of schemes `f : X ⟶ Y`, an open `V ⊆ Y`, a functor
`E : Dc ⥤ Mod(𝒪_X)` and a degree `n`, the composite

> `H^n(RΓ(V, Rf_*((E Z)[0]))) ⟶ Γ(V, H^n(Rf_*((E Z)[0]))) ⟶ Γ(V, R^n f_*(E Z))`

— the edge morphism of `RΓ(V, -)` at `Rf_*((E Z)[0])`, then `Γ(V, -)` of
`…TopDegreeBaseChange.homologyFunctorDerivedPushforwardIso` — is the inverse of the degree-`n`
cohomology of the Leray comparison of [Stacks, Tag 0D5W], then the crossing of the two models of
the iterated derived functor of `Γ(V, -) ∘ f_*` together with Grothendieck's comparison of
[Stacks, Tag 01XK] inverted, then `Γ(V, -)` of the comparison of the two indexings of the right
derived functors.

This is `Stacks.EdgeCompat.singleCompDerivedSections_hom_app_comp_rightDerivedCompNatIso_inv`,
whose last factor is `Γ(V, -)` of the **single-complex** crossing, with that crossing traded for
the `γ⁺` side's one by `singleCompDerivedCompHomologyIsoRightDerived_hom_app_eq` and the
resulting `Stacks.DerivedIndexing.rightDerivedIso` moved to the other side. Both crossings are
isomorphisms and so is `rightDerivedIso`, with no hypothesis; the only inverse taken as a
hypothesis is the Leray one, which `Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison`
supplies unconditionally, and it is taken as a left inverse of a plain morphism.

The functor `E` is kept general, and at the `SheafOfModules (structureSheafRing …)` spelling, for
the reason the mirror records: [Stacks, Tag 01XK] whiskers by the inclusion of the quasi-coherent
modules, and an `(𝟭 _).obj` in that slot triggers expensive unfolding. The crossing of the
`AlgebraicGeometry.Scheme.Modules` divide happens once, in argument position, where `E Z` is
handed to the scheme-level crossing. -/
theorem sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq
    (hpl : ∀ Z : Dc, (sectionsOverOpen Y.toSheafedSpace V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n))
    (Z : Dc)
    [(sectionsOverOpen Y.toSheafedSpace V).PreservesLeftHomologyOf
      ((((modulePushforward f.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℕ)).obj
        (injectiveResolution (E.obj Z)).cocomplex).sc n)]
    {lInv : (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedSectionsOverOpen Y.toSheafedSpace V).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
              (E.obj Z)))) ⟶
      (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedPreimageSections f.toLRSHom.toShHom V).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
            (E.obj Z)))}
    (hl : lInv ≫ (homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).map
          ((lerayComparison f.toLRSHom.toShHom V).app
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
              (E.obj Z))) = 𝟙 _) :
    (derivedHomologyComparison (sectionsOverOpen Y.toSheafedSpace V)
            (derivedSectionsOverOpen Y.toSheafedSpace V)
            (derivedSectionsOverOpenUnit Y.toSheafedSpace V)
            (exists_quasiIso_isKInjective Y.toSheafedSpace) (n : ℤ)).app
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
              (E.obj Z))) ≫
        (sectionsOverOpen Y.toSheafedSpace V).map
          (homologyFunctorDerivedPushforwardIso f (E.obj Z) (n : ℤ)).hom =
      lInv ≫ ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
              (modulePushforward f.toLRSHom.toShHom ⋙ sectionsOverOpen Y.toSheafedSpace V)
              (derivedPreimageSections f.toLRSHom.toShHom V)
              (Stacks.EdgeCompat.derivedPreimageSectionsUnitComp f.toLRSHom.toShHom V)
              (exists_quasiIso_isKInjective X.toSheafedSpace) n).hom.app (E.obj Z) ≫
            (Stacks.Cohomology.AffineBase.rightDerivedCompNatIso E
              (modulePushforward f.toLRSHom.toShHom) (sectionsOverOpen Y.toSheafedSpace V) n
              hpl).inv.app Z) ≫
          (sectionsOverOpen Y.toSheafedSpace V).map
            ((Stacks.DerivedIndexing.rightDerivedIso
              (modulePushforward f.toLRSHom.toShHom) n).hom.app (E.obj Z)) := by
  have hm := Stacks.EdgeCompat.singleCompDerivedSections_hom_app_comp_rightDerivedCompNatIso_inv
    f.toLRSHom.toShHom V E n hpl Z
  rw [singleCompDerivedCompHomologyIsoRightDerived_hom_app_eq f (E.obj Z) n] at hm
  have key := comp_map_eq (sectionsOverOpen Y.toSheafedSpace V) hl
    ((Stacks.DerivedIndexing.rightDerivedIso
      (modulePushforward f.toLRSHom.toShHom) n).inv_hom_id_app (E.obj Z)) hm
  exact key

/-! ### The tail through the edge morphism of a second direct image -/

/-- **A hoisted prefix cancelled against the leading crossing.** From `e ≫ G u = Pre` and
`u ≫ u' = 𝟙` one gets `Pre ≫ G (u' ≫ v) = e ≫ G v`. Stated at variables of abstract categories,
so that at the application the unifier meets the concrete crossing in argument position only and
never re-elaborates a composite spanning the `AlgebraicGeometry.Scheme.Modules` divide. -/
private theorem comp_map_cancel {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {P : D} {A A' B : C} {e : P ⟶ G.obj A} {u : A ⟶ A'} {u' : A' ⟶ A} (huu : u ≫ u' = 𝟙 A)
    {v : A ⟶ B} {Pre : P ⟶ G.obj A'} (hPre : e ≫ G.map u = Pre) :
    Pre ≫ G.map (u' ≫ v) = e ≫ G.map v := by
  rw [← hPre, Category.assoc, ← G.map_comp, ← Category.assoc u u' v, huu, Category.id_comp]

variable {Z'' : RingedSpace.{u, u}} (g : Z'' ⟶ Y.toSheafedSpace)

open Stacks.EdgeCompat

/-- **The `γ⁺` side's tail, from the leading crossing through the edge morphism of a second direct
image, read entirely in the model of derived sections over an open.** For a morphism of schemes
`f : X ⟶ Y`, an open `V ⊆ Y`, a functor `E : Dc ⥤ Mod(𝒪_X)`, a degree `n`, a morphism of ringed
spaces `g : Z'' ⟶ Y`, an object `K` of `D(𝒪_{Z''})` and **any** morphism
`β : Rf_*((E Z)[0]) ⟶ Rg_* K` of `D(𝒪_Y)`, the composite

> `Pre`, then `Γ(V, -)` of `…homologyFunctorDerivedPushforwardIso` inverted followed by `v`

is `H^n(RΓ(V, β))`, then the inverse of the degree-`n` cohomology of the Leray comparison of
[Stacks, Tag 0D5W] at `K`, then the edge morphism of `RΓ(g⁻¹V, -)` at `K`.

Here `Pre` is the prefix
`sectionsOverOpenHomologyComparison_comp_map_homologyFunctorDerivedPushforwardIso_hom_eq` computes
— the edge morphism of `RΓ(V, -)` at `Rf_*((E Z)[0])` followed by `Γ(V, -)` of the crossing —
hoisted onto a variable and fixed by `hPre`, and `v` is the rest of the tail, hoisted and fixed by
`hv`: the degree-`n` cohomology of `β` followed by the edge morphism of `Rg_*` at `K`. Hoisting
both is what keeps the crossing of the
`AlgebraicGeometry.Scheme.Modules` / `SheafOfModules (structureSheafRing …)` divide to one, in
argument position; written out, the statement crosses it twice and does not elaborate.

This composes the first three factors of the tail of [Stacks, Tag 0EX3] (c): the leading crossing
cancels against `Pre`, the naturality of the edge morphism of `RΓ(V, -)` carries it along `β`, and
the pair it then forms with `Γ(V, -)` of the edge morphism of `Rg_*` is absorbed. The only inverse
asked for is the Leray one, which
`Stacks.Cohomology.DerivedSectionsLeray.isIso_lerayComparison` supplies unconditionally, so
**nothing is assumed of `g`** — which is what the situation of (c) requires, since it places no
hypothesis on the morphism of bases. -/
theorem prefix_comp_map_inv_comp_eq_derivedPreimageSectionsHomologyComparison
    (Z : Dc)
    {Pre : (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedSectionsOverOpen Y.toSheafedSpace V).obj
          ((derivedPushforward f.toLRSHom.toShHom).obj
            ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
              (E.obj Z)))) ⟶
      (sectionsOverOpen Y.toSheafedSpace V).obj
        (((Scheme.Modules.pushforward f).rightDerivedPlus (n : ℤ)).obj (E.obj Z))}
    (hPre : (derivedHomologyComparison (sectionsOverOpen Y.toSheafedSpace V)
              (derivedSectionsOverOpen Y.toSheafedSpace V)
              (derivedSectionsOverOpenUnit Y.toSheafedSpace V)
              (exists_quasiIso_isKInjective Y.toSheafedSpace) (n : ℤ)).app
            ((derivedPushforward f.toLRSHom.toShHom).obj
              ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
                (E.obj Z))) ≫
          (sectionsOverOpen Y.toSheafedSpace V).map
            (homologyFunctorDerivedPushforwardIso f (E.obj Z) (n : ℤ)).hom = Pre)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing Z'')))
    (β : (derivedPushforward f.toLRSHom.toShHom).obj
        ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
          (E.obj Z)) ⟶ (derivedPushforward g).obj K)
    {v : (homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace))
          (n : ℤ)).obj
        ((derivedPushforward f.toLRSHom.toShHom).obj
          ((singleFunctor (SheafOfModules.{u} (structureSheafRing X.toSheafedSpace)) 0).obj
            (E.obj Z))) ⟶
      (modulePushforward g).obj
        ((homologyFunctor (SheafOfModules.{u} (structureSheafRing Z'')) (n : ℤ)).obj K)}
    (hv : (homologyFunctor (SheafOfModules.{u} (structureSheafRing Y.toSheafedSpace))
            (n : ℤ)).map β ≫
          (derivedPushforwardHomologyComparison g (n : ℤ)).app K = v)
    {lInv : (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedSectionsOverOpen Y.toSheafedSpace V).obj ((derivedPushforward g).obj K)) ⟶
      (homologyFunctor
          (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).obj
        ((derivedPreimageSections g V).obj K)}
    (hl : lInv ≫ (homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).map
          ((lerayComparison g V).app K) = 𝟙 _) :
    Pre ≫ (sectionsOverOpen Y.toSheafedSpace V).map
          ((homologyFunctorDerivedPushforwardIso f (E.obj Z) (n : ℤ)).inv ≫ v) =
      (homologyFunctor
            (ModuleCat.{u} ((structureSheafRing Y.toSheafedSpace).obj.obj (op V))) (n : ℤ)).map
          ((derivedSectionsOverOpen Y.toSheafedSpace V).map β) ≫
        lInv ≫ (derivedHomologyComparison
          (modulePushforward g ⋙ sectionsOverOpen Y.toSheafedSpace V)
          (derivedPreimageSections g V)
          (Stacks.EdgeCompat.derivedPreimageSectionsUnitComp g V)
          (exists_quasiIso_isKInjective Z'') (n : ℤ)).app K := by
  have hcancel := comp_map_cancel (sectionsOverOpen Y.toSheafedSpace V)
    ((homologyFunctorDerivedPushforwardIso f (E.obj Z) (n : ℤ)).hom_inv_id) hPre (v := v)
  rw [hcancel, ← hv]
  exact sectionsOverOpenHomologyComparison_comp_map_comp_derivedPushforwardHomologyComparison_eq
    g V (n : ℤ) K β hl

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
