module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

/-!
# Composition of derived pushforwards along morphisms of ringed spaces

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` and `g : (Y, 𝒪_Y) ⟶ (Z, 𝒪_Z)` be morphisms of ringed spaces.
Write `Rf_*`, `Rg_*` and `R(f ≫ g)_*` for right derived functors of the three degreewise
pushforwards followed by localization, each presented by a functor on derived categories
together with its canonical comparison and an `IsRightDerivedFunctor` instance.  The ordinary
pushforward-composition isomorphism and the universal property of `R(f ≫ g)_*` produce a
canonical comparison

`R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*`

and the assertion that it is invertible is the composition formula for derived pushforward.

The comparison is invertible exactly when the degreewise pushforward `f_*` carries K-injective
complexes of `𝒪_X`-modules to complexes that compute `Rg_*`.

## Main definitions

* `Stacks.Cohomology.DerivedPushforwardComposition.pushforwardToDerivedCategory` is degreewise
  pushforward on the homotopy category, followed by localization to the derived category.
* `Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompUnit` is the comparison
  from degreewise pushforward along `f ≫ g` to the composite of the two derived pushforwards.
* `Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardComparison` is the induced
  canonical comparison `R(f ≫ g)_* ⟶ Rf_* ⋙ Rg_*`.
* `Stacks.Cohomology.DerivedPushforwardComposition.PushforwardComputesDerived` is the property that
  `g_* (f_* I) ⟶ Rg_* (f_* I)` is invertible for every K-injective complex `I` of `𝒪_X`-modules.

## Main results

* `Stacks.Cohomology.DerivedPushforwardComposition.isRightDerivedFunctor_comp`: under
  `PushforwardComputesDerived`, the composite `Rf_* ⋙ Rg_*` together with
  `derivedPushforwardCompUnit` is a right derived functor of degreewise pushforward along `f ≫ g`.
* `Stacks.Cohomology.DerivedPushforwardComposition.isIso_derivedPushforwardComparison`: under
  `PushforwardComputesDerived`, the canonical comparison is an isomorphism.
* `Stacks.Cohomology.DerivedPushforwardComposition.derivedPushforwardCompIso`: the resulting
  natural isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*`.
* `Stacks.Cohomology.DerivedPushforwardComposition.isIso_derivedPushforwardComparison_iff`: the
  converse too, so that `PushforwardComputesDerived` is equivalent to the composition formula.
* `Stacks.Cohomology.DerivedPushforwardComposition.pushforwardComputesDerived_of_isKInjective`: a
  pushforward that preserves K-injectivity satisfies the hypothesis.

## References

* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
-/


@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.DerivedPushforwardComposition

export RingedSpaceModuleAdjunction (ModuleSheaves)

universe u wX wY wZ


/-- Degreewise pushforward on the unbounded homotopy category, followed by localization to the
derived category.  A right derived functor of this functor is a derived pushforward `Rf_*`. -/
noncomputable abbrev pushforwardToDerivedCategory
    {X Y : RingedSpace.{u, u}} [HasDerivedCategory.{wY} (ModuleSheaves Y)]
    (f : X ⟶ Y) :
    HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ) ⥤
      DerivedCategory (ModuleSheaves Y) :=
  (modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh

/-- The comparison from degreewise pushforward along `f ≫ g` to the composite of the derived
pushforwards along `f` and `g`.

It is the pushforward-composition isomorphism, followed by the comparison for `Rg_*` and then
by the comparison for `Rf_*`, in that order. -/
noncomputable def derivedPushforwardCompUnit {X Y Z : RingedSpace.{u, u}}
    [HasDerivedCategory.{wX} (ModuleSheaves X)]
    [HasDerivedCategory.{wY} (ModuleSheaves Y)]
    [HasDerivedCategory.{wZ} (ModuleSheaves Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (Rf : DerivedCategory (ModuleSheaves X) ⥤ DerivedCategory (ModuleSheaves Y))
    (Rg : DerivedCategory (ModuleSheaves Y) ⥤ DerivedCategory (ModuleSheaves Z))
    (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
    (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg) :
    pushforwardToDerivedCategory (f ≫ g) ⟶ DerivedCategory.Qh ⋙ (Rf ⋙ Rg) :=
  Functor.whiskerRight
      (Functor.mapHomotopyCategoryCompIso (modulePushforwardComp f g)
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft
      ((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)) αg ≫
    Functor.whiskerRight αf Rg

/-- The value of `derivedPushforwardCompUnit` at an object of the homotopy category, written out as
a composite of three maps. -/
theorem derivedPushforwardCompUnit_app {X Y Z : RingedSpace.{u, u}}
    [HasDerivedCategory.{wX} (ModuleSheaves X)]
    [HasDerivedCategory.{wY} (ModuleSheaves Y)]
    [HasDerivedCategory.{wZ} (ModuleSheaves Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (Rf : DerivedCategory (ModuleSheaves X) ⥤ DerivedCategory (ModuleSheaves Y))
    (Rg : DerivedCategory (ModuleSheaves Y) ⥤ DerivedCategory (ModuleSheaves Z))
    (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
    (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)
    (K : HomotopyCategory (ModuleSheaves X) (ComplexShape.up ℤ)) :
    (derivedPushforwardCompUnit f g Rf Rg αf αg).app K =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso (modulePushforwardComp f g)
            (ComplexShape.up ℤ)).inv.app K) ≫
        αg.app (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        Rg.map (αf.app K) :=
  rfl

/-- The property that degreewise pushforward along `f` carries the K-injective complexes of
`𝒪_X`-modules to complexes computing the derived pushforward along `g`: the comparison
`g_* (f_* I) ⟶ Rg_* (f_* I)` is invertible for every K-injective `I`. -/
abbrev PushforwardComputesDerived {X Y Z : RingedSpace.{u, u}}
    [HasDerivedCategory.{wY} (ModuleSheaves Y)]
    [HasDerivedCategory.{wZ} (ModuleSheaves Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (Rg : DerivedCategory (ModuleSheaves Y) ⥤ DerivedCategory (ModuleSheaves Z))
    (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg) : Prop :=
  ∀ I : CochainComplex (ModuleSheaves X) ℤ, I.IsKInjective →
    IsIso (αg.app (((modulePushforward f).mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj I)))

/-- The middle factor of a three-fold composite is invertible as soon as the composite and the two
outer factors are. -/
theorem isIso_middle_of_comp {C : Type*} [Category C] {W X Y Z : C} {a : W ⟶ X} {b : X ⟶ Y}
    {c : Y ⟶ Z} [IsIso a] [IsIso c] (h : IsIso (a ≫ b ≫ c)) : IsIso b :=
  have := h
  have : IsIso (b ≫ c) := IsIso.of_isIso_comp_left a (b ≫ c)
  IsIso.of_isIso_comp_right b c

section

variable {X Y Z : RingedSpace.{u, u}}
    [HasDerivedCategory.{wX} (ModuleSheaves X)]
    [HasDerivedCategory.{wY} (ModuleSheaves Y)]
    [HasDerivedCategory.{wZ} (ModuleSheaves Z)]
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (Rf : DerivedCategory (ModuleSheaves X) ⥤ DerivedCategory (ModuleSheaves Y))
    (Rg : DerivedCategory (ModuleSheaves Y) ⥤ DerivedCategory (ModuleSheaves Z))
    (Rgf : DerivedCategory (ModuleSheaves X) ⥤ DerivedCategory (ModuleSheaves Z))
    (αf : pushforwardToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ Rf)
    (αg : pushforwardToDerivedCategory g ⟶ DerivedCategory.Qh ⋙ Rg)
    (αgf : pushforwardToDerivedCategory (f ≫ g) ⟶ DerivedCategory.Qh ⋙ Rgf)

/-- The canonical comparison from a derived pushforward along `f ≫ g` to the composite of
derived pushforwards along `f` and `g`, obtained from the universal property of the former.

By `CategoryTheory.Functor.rightDerived_fac`, precomposing it with `αgf` returns
`derivedPushforwardCompUnit f g Rf Rg αf αg`, which characterizes it. -/
noncomputable def derivedPushforwardComparison
    [Rgf.IsRightDerivedFunctor αgf
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    Rgf ⟶ Rf ⋙ Rg :=
  Rgf.rightDerivedDesc αgf
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) _
    (derivedPushforwardCompUnit f g Rf Rg αf αg)

/-- A K-injective complex computes any derived pushforward: the comparison of a right derived
functor of degreewise pushforward is invertible there. -/
theorem isIso_app_of_isKInjective
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    (I : CochainComplex (ModuleSheaves X) ℤ) (hI : I.IsKInjective) :
    IsIso (αf.app ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, wY, wX, u + 1, u + 1, u + 1}
      (pushforwardToDerivedCategory f)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)).2
    DerivedCategory.Qh Rf αf I hI

omit [HasDerivedCategory.{wX} (ModuleSheaves X)] in
/-- If the comparison `αg` of a derived pushforward along `g` is invertible, then every complex
computes it, so `PushforwardComputesDerived f g Rg αg` holds. -/
theorem pushforwardComputesDerived_of_isIso (h : IsIso αg) :
    PushforwardComputesDerived f g Rg αg :=
  have := h
  fun _ _ => NatIso.isIso_app_of_isIso αg _

omit [HasDerivedCategory.{wX} (ModuleSheaves X)] in
/-- If degreewise pushforward along `f` preserves K-injectivity, then it carries K-injective
complexes to complexes computing the derived pushforward along `g`. -/
theorem pushforwardComputesDerived_of_isKInjective
    [Rg.IsRightDerivedFunctor αg
      (HomotopyCategory.quasiIso (ModuleSheaves Y) (ComplexShape.up ℤ))]
    (h : ∀ I : CochainComplex (ModuleSheaves X) ℤ, I.IsKInjective →
      CochainComplex.IsKInjective
        (((modulePushforward f).mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    PushforwardComputesDerived f g Rg αg :=
  fun I hI => isIso_app_of_isKInjective g Rg αg _ (h I hI)

/-- **The composite of two derived pushforwards is a derived pushforward along the composite.**
Under `PushforwardComputesDerived`, the composite `Rf_* ⋙ Rg_*`, with the comparison
`derivedPushforwardCompUnit`, is a right derived functor of degreewise pushforward along `f ≫ g`.
-/
theorem isRightDerivedFunctor_comp
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    (h : PushforwardComputesDerived f g Rg αg) :
    (Rf ⋙ Rg).IsRightDerivedFunctor (derivedPushforwardCompUnit f g Rf Rg αf αg)
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) := by
  refine
    isRightDerivedFunctor_of_isIso_app_isKInjective.{
      u, wZ, wX, u + 1, u + 1, u + 1}
    (pushforwardToDerivedCategory (f ≫ g))
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)
    DerivedCategory.Qh _ _ fun I hI => ?_
  rw [derivedPushforwardCompUnit_app]
  have h₂ := h I hI
  have h₃ := isIso_app_of_isKInjective f Rf αf I hI
  infer_instance

/-- **The composition formula.** Under `PushforwardComputesDerived`, the canonical comparison from
a derived pushforward along `f ≫ g` to the composite of derived pushforwards along `f` and `g` is
an isomorphism. -/
theorem isIso_derivedPushforwardComparison
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [Rgf.IsRightDerivedFunctor αgf
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    (h : PushforwardComputesDerived f g Rg αg) :
    IsIso (derivedPushforwardComparison f g Rf Rg Rgf αf αg αgf) :=
  (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc Rgf αgf
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) (Rf ⋙ Rg)
      (derivedPushforwardCompUnit f g Rf Rg αf αg)).1
    (isRightDerivedFunctor_comp f g Rf Rg αf αg h)

/-- The natural isomorphism `Rf_* ⋙ Rg_* ≅ R(f ≫ g)_*` obtained by inverting the canonical
comparison. -/
noncomputable def derivedPushforwardCompIso
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [Rgf.IsRightDerivedFunctor αgf
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    (h : PushforwardComputesDerived f g Rg αg) :
    Rf ⋙ Rg ≅ Rgf :=
  haveI := isIso_derivedPushforwardComparison f g Rf Rg Rgf αf αg αgf h
  (asIso (derivedPushforwardComparison f g Rf Rg Rgf αf αg αgf)).symm

/-- The canonical comparison from a derived pushforward along `f ≫ g` to the composite of derived
pushforwards along `f` and `g` is an isomorphism exactly when degreewise pushforward along `f`
carries K-injective complexes to complexes computing the derived pushforward along `g`. -/
theorem isIso_derivedPushforwardComparison_iff
    [Rf.IsRightDerivedFunctor αf
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))]
    [Rgf.IsRightDerivedFunctor αgf
      (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ))] :
    IsIso (derivedPushforwardComparison f g Rf Rg Rgf αf αg αgf) ↔
      PushforwardComputesDerived f g Rg αg := by
  refine ⟨fun hiso I hI => ?_, isIso_derivedPushforwardComparison f g Rf Rg Rgf αf αg αgf⟩
  have hgf := isIso_app_of_isKInjective (f ≫ g) Rgf αgf I hI
  have h₃ := isIso_app_of_isKInjective f Rf αf I hI
  have hfac := Functor.rightDerived_fac_app Rgf αgf
    (HomotopyCategory.quasiIso (ModuleSheaves X) (ComplexShape.up ℤ)) (Rf ⋙ Rg)
    (derivedPushforwardCompUnit f g Rf Rg αf αg)
    ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj I)
  have hunit := IsIso.comp_isIso' hgf
    (NatIso.isIso_app_of_isIso (derivedPushforwardComparison f g Rf Rg Rgf αf αg αgf)
      (DerivedCategory.Qh.obj
        ((HomotopyCategory.quotient (ModuleSheaves X) (ComplexShape.up ℤ)).obj I)))
  rw [derivedPushforwardComparison, hfac, derivedPushforwardCompUnit_app] at hunit
  exact isIso_middle_of_comp hunit

end

end Stacks.Cohomology.DerivedPushforwardComposition

end
