module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasquePushforwardVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
public import StacksFrontier.Topology.Sheaves.Functors.Module.EnoughInjectives
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The acyclicity input of the relative Leray spectral sequence

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of ringed spaces. The relative Leray spectral
sequence of [Stacks, Tag 01F6] is the Grothendieck spectral sequence of [Stacks, Tag 015N]
for the pair `(f_*, g_*)`, and the hypothesis that pair has to satisfy is that `f_* ℐ` is
right acyclic for `g_*` whenever `ℐ` is an injective `𝒪_X`-module. This file proves that
hypothesis, and records the one identification the abutment needs.

The route is flasqueness. An injective sheaf of modules has surjective restriction maps
([Stacks, Tag 01EA]); the sections of `f_* ℐ` over an open `V` of `Y` are the sections of `ℐ`
over `f⁻¹ V`, so `f_* ℐ` again has surjective restriction maps; and a flasque sheaf of modules
has vanishing positive higher direct images along any morphism of ringed spaces
([Stacks, Tag 09T0]). Pushforward is a right adjoint, hence left exact, so part (2) of
[Stacks, Tag 015C] turns that vanishing into right acyclicity.

## Main results

* `Stacks.RelativeLeray.modulePushforward_comp`: `f_* ⋙ g_* = (f ≫ g)_*`, on the nose. The
  two sides are *equal*, not merely isomorphic, so the abutment of the Grothendieck spectral
  sequence for `(f_*, g_*)` is literally the higher direct image along `f ≫ g` and no
  comparison isomorphism is involved anywhere below.
* `Stacks.RelativeLeray.isFlasque_modulePushforward`: the pushforward of a flasque sheaf of
  modules is flasque.
* `Stacks.RelativeLeray.isZero_rightDerivedPlus_modulePushforward_obj_injective`:
  `R ᵖ g_*(f_* ℐ) = 0` for `p > 0` and `ℐ` injective.
* `Stacks.RelativeLeray.rightAcyclic_modulePushforward_obj_injective`: `f_* ℐ` is right
  acyclic for `g_*` when `ℐ` is injective. **This is the hypothesis `hFG` of
  `CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`
  ([Stacks, Tag 015N]) for the pair `(f_*, g_*)`.**

## Implementation notes

Flasqueness is imposed and concluded on the underlying sheaf of abelian groups, as in
[Stacks, Tag 09T0] and [Stacks, Tag 09SY]; `TopCat.Presheaf.IsFlasque` is a class, so the
hypothesis is passed explicitly and re-installed with `let` where an instance is wanted.

`isFlasque_modulePushforward` needs no computation: by construction the restriction map of
`f_* F` from `V` to `V' ⊆ V` *is* the restriction map of `F` from `f⁻¹ V` to `f⁻¹ V'`, so the
epimorphism asked for is one of the epimorphisms assumed. This is why the lemma is three lines
and the corresponding step of
`Stacks.Cohomology.PushforwardAcyclic.pushforward_injective_rightAcyclic` is not: that proof
chases a section through `AddCommGrpCat.epi_iff_surjective` because it starts from
surjectivity of the restriction maps of `ℐ` rather than from their epimorphy.  Flasqueness of
the pushforward of an *injective* module, which is what the vanishing below needs, is
`Stacks.Cohomology.PushforwardAcyclic.modulePushforward_underlying_isFlasque`.

`HasDerivedCategory.standard` is a local instance: there is no global one.

## References

* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015N](https://stacks.math.columbia.edu/tag/015N)
* [Stacks Project, Tag 01F6](https://stacks.math.columbia.edu/tag/01F6)
* [Stacks Project, Tag 09T0](https://stacks.math.columbia.edu/tag/09T0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.RelativeLeray

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- Pushforward of sheaves of modules is a right adjoint, hence preserves finite limits. -/
instance preservesFiniteLimits_modulePushforward {X Y : RingedSpace.{u, u}} (f : X ⟶ Y) :
    PreservesFiniteLimits (modulePushforward f) :=
  have : (modulePushforward f).IsRightAdjoint := modulePushforward_isRightAdjoint f
  inferInstance

/-- **Pushforward of modules is strictly functorial.** For composable morphisms of ringed
spaces, `f_* ⋙ g_*` and `(f ≫ g)_*` are the same functor, not merely isomorphic ones: both are
`SheafOfModules.pushforward` for the inverse-image functor `Opens Z ⥤ Opens X` and the induced
morphism of structure sheaves, and `Mathlib`'s `SheafOfModules.pushforwardComp` is the identity
isomorphism. -/
theorem modulePushforward_comp {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    modulePushforward f ⋙ modulePushforward g = modulePushforward (f ≫ g) :=
  rfl

/-- **The pushforward of a flasque sheaf of modules is flasque.** The restriction map of
`f_* F` along `V' ≤ V` is the restriction map of `F` along `f⁻¹ V' ≤ f⁻¹ V`. -/
@[sga "4 V 4.9" "special case"]
theorem isFlasque_modulePushforward {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
    (F : SheafOfModules.{u} (structureSheafRing X))
    (hF : TopCat.Presheaf.IsFlasque (X := TopCat.of X.carrier)
      ((SheafOfModules.toSheaf (structureSheafRing X)).obj F).obj) :
    TopCat.Presheaf.IsFlasque (X := TopCat.of Y.carrier)
      ((SheafOfModules.toSheaf (structureSheafRing Y)).obj ((modulePushforward f).obj F)).obj where
  epi {U V} i :=
    hF.epi (U := op ((opensMap f).obj U.unop)) (V := op ((opensMap f).obj V.unop))
      ((opensMap f).map i.unop).op

/-- **An injective sheaf of modules is flasque.** This is [Stacks, Tag 01EA] read as
epimorphy of the restriction maps of the underlying sheaf of abelian groups. -/
theorem isFlasque_of_injective (X : RingedSpace.{u, u})
    (I : SheafOfModules.{u} (structureSheafRing X)) [Injective I] :
    TopCat.Presheaf.IsFlasque (X := TopCat.of X.carrier)
      ((SheafOfModules.toSheaf (structureSheafRing X)).obj I).obj where
  epi {_ _} i := (AddCommGrpCat.epi_iff_surjective _).2
    (Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective
      (structureSheafRing X) I (leOfHom i.unop))

/-- **The higher direct images of the pushforward of an injective module vanish.** For
composable morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of ringed spaces and `ℐ` an injective
`𝒪_X`-module, `R ᵖ g_*(f_* ℐ) = 0` for every `p > 0`: the module `f_* ℐ` is flasque, and
[Stacks, Tag 09T0] applies to it. -/
theorem isZero_rightDerivedPlus_modulePushforward_obj_injective
    {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : SheafOfModules.{u} (structureSheafRing X)) [Injective I] (p : ℤ) (hp : 0 < p) :
    IsZero (((modulePushforward g).rightDerivedPlus p).obj ((modulePushforward f).obj I)) :=
  let _ : TopCat.Presheaf.IsFlasque (X := TopCat.of Y.carrier)
      ((SheafOfModules.toSheaf (structureSheafRing Y)).obj ((modulePushforward f).obj I)).obj :=
    Stacks.Cohomology.PushforwardAcyclic.modulePushforward_underlying_isFlasque f I
  Stacks.Cohomology.FlasquePushforward.isZero_rightDerivedPlus_modulePushforward_of_isFlasque
    g ((modulePushforward f).obj I) p hp

/-- **The acyclicity hypothesis of the relative Leray spectral sequence.** For composable
morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of ringed spaces, the pushforward along `f` of an
injective `𝒪_X`-module is right acyclic for the pushforward along `g`.

This is the hypothesis `hFG` of
`CategoryTheory.Functor.exists_spectralSequence_rightDerivedFunctorPlus_comp`
([Stacks, Tag 015N]) for the pair `(f_*, g_*)`, and hence the acyclicity input of
[Stacks, Tag 01F6]. -/
theorem rightAcyclic_modulePushforward_obj_injective
    {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (I : SheafOfModules.{u} (structureSheafRing X)) [Injective I] :
    (modulePushforward g).rightAcyclic ((modulePushforward f).obj I) :=
  ((Functor.rightAcyclic_iff_isIso_and_isZero_rightDerivedPlus (modulePushforward g)
      ((modulePushforward f).obj I)).2 inferInstance).2
    fun p hp => isZero_rightDerivedPlus_modulePushforward_obj_injective f g I p hp

end Stacks.RelativeLeray

end
