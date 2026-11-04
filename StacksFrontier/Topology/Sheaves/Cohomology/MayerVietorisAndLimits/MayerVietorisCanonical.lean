module

public import StacksFrontier.Topology.Sheaves.Cohomology.MayerVietorisAndLimits.MayerVietoris

/-!
# The Mayer--Vietoris triangle of a two-open cover, with no derived functor assumed

`Stacks.Cohomology.MayerVietoris.exists_distinguished_triangle_of_cover` proves Stacks 08BV for an
arbitrary triple of right derived functors of `ℱ ↦ j_{U*}(ℱ|_U)`, `ℱ ↦ j_{V*}(ℱ|_V)` and
`ℱ ↦ j_{(U ∩ V)*}(ℱ|_{U ∩ V})`, supplied together with their comparison maps. This file removes
that input: the three functors `Rj_{U*}`, `Rj_{V*}`, `Rj_{(U ∩ V)*}` are constructed here on the
whole unbounded derived category `D(O)`, so the triangle becomes a function of the sheaf of rings
and the cover alone.

## Main definitions

* `Stacks.Cohomology.MayerVietoris.rightDerivedRestrictPush`: the functor
  `Rj_{U*}(-|_U) : D(O) ⥤ D(O)`, the total right derived functor of `ℱ ↦ j_{U*}(ℱ|_U)`, with
  comparison `Stacks.Cohomology.MayerVietoris.rightDerivedRestrictPushUnit`.

## Main results

* `Stacks.Cohomology.MayerVietoris.hasPointwiseRightDerivedFunctor_of_homotopyCategory`: every
  functor out of `K(O)` has a pointwise right derived functor along the localization to `D(O)`.
* `Stacks.Cohomology.MayerVietoris.rightDerivedRestrictPush_isRightDerivedFunctor`: the
  constructed functor is a right derived functor of `ℱ ↦ j_{U*}(ℱ|_U)`, so it may be substituted
  for the functors that Stacks 08BV was proved for.
* `Stacks.Cohomology.MayerVietoris.exists_distinguished_triangle_of_cover_rightDerived`:
  **Stacks 08BV** for the constructed functors -- the distinguished Mayer--Vietoris triangle of a
  cover by two opens, functorial in the object of `D(O)`, with no derived functor, comparison map
  or derived-functor hypothesis taken as a parameter.

## Implementation notes

The existence input is the K-injective criterion of Stacks 070K, stated in `CategoryTheory` as
`Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective`, whose
hypothesis is that every complex of `O`-modules receives a quasi-isomorphism into a K-injective
complex. For modules over a sheaf of rings on a topological space that is unconditional: the
category is Grothendieck abelian, so the functorial resolution of Stacks 079P applies, which is
`Stacks.Cohomology.RestrictionCover.exists_quasiIso_kInjective`. Nothing about the functor being
derived is used, not even additivity, so the three functors of the triangle are instances of one
construction and are canonical simultaneously.

The construction is the same as
`Stacks.Cohomology.RelativeMayerVietoris.canonicalRightDerived`, which is stated for an additive
functor between the module categories of two ringed spaces. It is restated here at the generality
of the Mayer--Vietoris file -- modules over a sheaf of possibly noncommutative rings on a
topological space -- which is the generality in which `Rj_{U*}` has to be formed for Stacks 08BV,
and which is not reached by instantiating the ringed-space statement.

## References

* [Stacks Project, Tag 08BV](https://stacks.math.columbia.edu/tag/08BV)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open Stacks.Cohomology.RestrictionCover

universe v' u' u

namespace Stacks.Cohomology.MayerVietoris

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] CategoryTheory.Abelian.hasFiniteLimits

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Sheaves of modules on a ringed space form a Grothendieck abelian category at the universe of
the space. The universe has to be pinned: typeclass inference cannot determine it from the goals
in which it is used below. -/
private local instance grothendieckAbelianAtSpaceUniverse
    {O : Sheaf (Opens.grothendieckTopology X) RingCat.{u}} :
    IsGrothendieckAbelian.{u} (SheafOfModules.{u} O) :=
  inferInstance

/-! ### The right derived functor of a functor on the homotopy category -/

/-- **Every functor out of the unbounded homotopy category of `O`-modules has a pointwise right
derived functor** along the localization at the quasi-isomorphisms. This is the K-injective
criterion of Stacks 070K, whose hypothesis holds unconditionally here because
`SheafOfModules O` is Grothendieck abelian. -/
theorem hasPointwiseRightDerivedFunctor_of_homotopyCategory {H : Type u'} [Category.{v'} H]
    (G : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ) ⥤ H) :
    G.HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, v', u, u + 1, u', u + 1} G
    (exists_quasiIso_kInjective (SheafOfModules.{u} O))).1

/-- The degreewise functor `ℱ ↦ j_{U*}(ℱ|_U)`, localized to `D(O)`, has a right derived
functor. -/
instance restrictPush_hasRightDerivedFunctor (U : Opens X) :
    (homotopyToDerived O U).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  have := hasPointwiseRightDerivedFunctor_of_homotopyCategory O (homotopyToDerived O U)
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- **`Rj_{U*}(-|_U) : D(O) ⥤ D(O)`**, the total right derived functor of the degreewise functor
`ℱ ↦ j_{U*}(ℱ|_U)` followed by the localization to the derived category. -/
def rightDerivedRestrictPush (U : Opens X) :
    DerivedCategory (SheafOfModules.{u} O) ⥤ DerivedCategory (SheafOfModules.{u} O) :=
  (homotopyToDerived O U).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))

/-- The canonical comparison `j_{U*}(-|_U) ⟶ Rj_{U*}(-|_U)`. -/
def rightDerivedRestrictPushUnit (U : Opens X) :
    homotopyToDerived O U ⟶ DerivedCategory.Qh ⋙ rightDerivedRestrictPush O U :=
  (homotopyToDerived O U).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ))

/-- `Rj_{U*}(-|_U)` with its canonical comparison is a right derived functor of
`ℱ ↦ j_{U*}(ℱ|_U)`. This is what lets it be substituted for the derived functors that
Stacks 08BV was proved for. -/
instance rightDerivedRestrictPush_isRightDerivedFunctor (U : Opens X) :
    (rightDerivedRestrictPush O U).IsRightDerivedFunctor (rightDerivedRestrictPushUnit O U)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (((homotopyToDerived O U).totalRightDerived DerivedCategory.Qh
        _).IsRightDerivedFunctor
      ((homotopyToDerived O U).totalRightDerivedUnit DerivedCategory.Qh _) _)

/-! ### The triangle -/

/-- **Stacks 08BV.** A two-open cover of a space carrying a sheaf of rings `O` gives a
distinguished Mayer--Vietoris triangle

`E ⟶ Rj_{U*}(E|_U) ⊞ Rj_{V*}(E|_V) ⟶ Rj_{(U ∩ V)*}(E|_{U ∩ V}) ⟶ E⟦1⟧`

naturally in the object `E` of the unbounded derived category of `O`-modules, where the three
derived pushforwards are the ones constructed by `rightDerivedRestrictPush`. The restriction maps
`rU`, `rV`, the two difference maps `dU`, `dV` and the connecting map `δ` are maps of functors on
`D(O)`, which is the naturality in `E`, and the equations preceding the triangle identify them
with the restriction and transition maps of the cover through the canonical comparisons, so that
the triangle's maps and its Mayer--Vietoris sign are retained rather than merely asserted to
exist. -/
@[stacks 08BV "the ringed-space form with the three derived pushforwards constructed by \
`rightDerivedRestrictPush`, at the standard model of `D(O)`: no derived functor, comparison map \
or derived-functor hypothesis is taken as a parameter"]
theorem exists_distinguished_triangle_of_cover_rightDerived
    (U V : Opens X) (hUV : U ⊔ V = ⊤) :
    ∃ (qU : homotopyToDerived O U ⟶ homotopyToDerived O (U ⊓ V))
      (qV : homotopyToDerived O V ⟶ homotopyToDerived O (U ⊓ V))
      (rU : (CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)) :
        DerivedCategory (SheafOfModules.{u} O) ⥤
          DerivedCategory (SheafOfModules.{u} O)) ⟶ rightDerivedRestrictPush O U)
      (rV : (CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)) :
        DerivedCategory (SheafOfModules.{u} O) ⥤
          DerivedCategory (SheafOfModules.{u} O)) ⟶ rightDerivedRestrictPush O V)
      (dU : rightDerivedRestrictPush O U ⟶ rightDerivedRestrictPush O (U ⊓ V))
      (dV : rightDerivedRestrictPush O V ⟶ rightDerivedRestrictPush O (U ⊓ V))
      (δ : rightDerivedRestrictPush O (U ⊓ V) ⟶
        (CategoryTheory.Functor.id (DerivedCategory (SheafOfModules.{u} O)) :
          DerivedCategory (SheafOfModules.{u} O) ⥤
            DerivedCategory (SheafOfModules.{u} O)) ⋙
        shiftFunctor (DerivedCategory (SheafOfModules.{u} O)) (1 : ℤ)),
      homotopyRestriction O U ≫ qU = homotopyRestriction O (U ⊓ V) ∧
      homotopyRestriction O V ≫ qV = homotopyRestriction O (U ⊓ V) ∧
      homotopyRestriction O U ≫ rightDerivedRestrictPushUnit O U =
        Functor.whiskerLeft DerivedCategory.Qh rU ∧
      homotopyRestriction O V ≫ rightDerivedRestrictPushUnit O V =
        Functor.whiskerLeft DerivedCategory.Qh rV ∧
      qU ≫ rightDerivedRestrictPushUnit O (U ⊓ V) =
        rightDerivedRestrictPushUnit O U ≫ Functor.whiskerLeft DerivedCategory.Qh dU ∧
      -(qV ≫ rightDerivedRestrictPushUnit O (U ⊓ V)) =
        rightDerivedRestrictPushUnit O V ≫ Functor.whiskerLeft DerivedCategory.Qh dV ∧
      ∀ E, Triangle.mk (biprod.lift (rU.app E) (rV.app E))
        (biprod.desc (dU.app E) (dV.app E)) (δ.app E) ∈
          distTriang (DerivedCategory (SheafOfModules.{u} O)) :=
  exists_distinguished_triangle_of_cover O U V hUV
    (rightDerivedRestrictPush O U) (rightDerivedRestrictPush O V)
    (rightDerivedRestrictPush O (U ⊓ V))
    (rightDerivedRestrictPushUnit O U) (rightDerivedRestrictPushUnit O V)
    (rightDerivedRestrictPushUnit O (U ⊓ V))

end Stacks.Cohomology.MayerVietoris

end
