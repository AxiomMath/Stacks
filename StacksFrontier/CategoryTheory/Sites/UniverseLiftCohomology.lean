module

public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjectiveSmallSite
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftInjective
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftFirstCohomology

/-!
# Sheaf cohomology does not depend on the coefficient universe

Let `J` be a Grothendieck topology on a category `C`, and let `F` be a sheaf of abelian groups on
`C` with sections in `Type t`. Raising the universe of all its groups of sections gives a sheaf
`F ⋙ uliftFunctor` with sections in `Type (max t s)`. This file shows that the two have the same
cohomology,

  `H ^ n (C, F) ≃+ H ^ n (C, F ⋙ uliftFunctor)`,

as soon as the smaller sheaf category has enough injectives and the universe lift carries
injective sheaves to injective sheaves.

## Main definitions

* `Stacks.Sheaves.UniverseLift.uliftSheafFunctorConstantSheafIso`: the universe lift of a constant
  sheaf is the constant sheaf on the universe lift of its value.
* `Stacks.Sheaves.UniverseLift.uliftSheafFunctorConstantIntIso`: in particular the universe lift
  of the constant sheaf `ℤ` is the constant sheaf `ℤ`.
* `Stacks.Sheaves.UniverseLift.sheafHUliftAddEquiv`: **the comparison of cohomology.**

## Main results

* `Stacks.Sheaves.UniverseLift.bijective_mapExtAddHom_uliftSheafFunctor`: the universe lift is
  bijective on every `Ext` group.

## Implementation notes

The universe lift `L` is exact — it preserves limits because limits of sheaves are computed in
presheaves, and colimits because it commutes with sheafification
(`Stacks.Sheaves.UniverseLift.sheafCompose_uliftFunctor_preservesColimits`) — and it is fully
faithful. Mathlib's `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects` then
makes it bijective on `Ext`, given enough injectives in the source and preservation of injective
objects. The cohomology `CategoryTheory.Sheaf.H` is `Ext` out of the constant sheaf `ℤ`, and `L`
carries that constant sheaf to the constant sheaf `ℤ` again, because it commutes with
sheafification; precomposing with that isomorphism finishes the comparison.

Preservation of injective objects is a hypothesis here, an instance argument. It holds on a small
site (`Stacks.Cohomology.CoefficientLowering.sheafCompose_preservesInjectiveObjects`), and from
there on every site with a small dense subsite
(`Stacks.Sheaves.UniverseLift.preservesInjectiveObjects_uliftSheafFunctor_of_isEquivalence`); the
small étale site of a scheme is one, through its affine objects.

The two `Ext` universes are independent of each other and of the coefficient universes.

## References

* [Stacks Project, Tag 01FT](https://stacks.math.columbia.edu/tag/01FT): sheaf cohomology as a
  right derived functor, which does not see the universe its coefficients are taken in.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w₁ w₂ s t v u

namespace Stacks.Sheaves.UniverseLift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The universe lift of the group `ULift ℤ` is again `ULift ℤ`. -/
def uliftFunctorULiftIntIso :
    AddCommGrpCat.uliftFunctor.{s, t}.obj (AddCommGrpCat.of (ULift.{t} ℤ)) ≅
      AddCommGrpCat.of (ULift.{max t s} ℤ) :=
  (AddEquiv.ulift.trans (AddEquiv.ulift.trans AddEquiv.ulift.symm)).toAddCommGrpIso

variable [HasSheafify J AddCommGrpCat.{t}] [HasSheafify J AddCommGrpCat.{max t s}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t s}]

/-- **The universe lift of a constant sheaf is constant**: it is the constant sheaf on the
universe lift of the value, because the universe lift commutes with sheafification. -/
def uliftSheafFunctorConstantSheafIso (M : AddCommGrpCat.{t}) :
    (uliftSheafFunctor.{s, t} J).obj ((constantSheaf J AddCommGrpCat.{t}).obj M) ≅
      (constantSheaf J AddCommGrpCat.{max t s}).obj (AddCommGrpCat.uliftFunctor.{s, t}.obj M) :=
  have := preservesSheafification_uliftFunctor.{u, v, t, s} (J := J)
  ((sheafComposeNatIso J AddCommGrpCat.uliftFunctor.{s, t}
      (sheafificationAdjunction J AddCommGrpCat.{t})
      (sheafificationAdjunction J AddCommGrpCat.{max t s})).app
      ((Functor.const Cᵒᵖ).obj M)).symm ≪≫
    (presheafToSheaf J AddCommGrpCat.{max t s}).mapIso
      (Functor.constComp Cᵒᵖ M AddCommGrpCat.uliftFunctor.{s, t})

/-- **The universe lift of the constant sheaf `ℤ` is the constant sheaf `ℤ`.** -/
def uliftSheafFunctorConstantIntIso :
    (uliftSheafFunctor.{s, t} J).obj
        ((constantSheaf J AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift.{t} ℤ))) ≅
      (constantSheaf J AddCommGrpCat.{max t s}).obj (AddCommGrpCat.of (ULift.{max t s} ℤ)) :=
  uliftSheafFunctorConstantSheafIso.{s, t} J _ ≪≫
    (constantSheaf J AddCommGrpCat.{max t s}).mapIso uliftFunctorULiftIntIso.{s, t}

variable [EnoughInjectives (Sheaf J AddCommGrpCat.{t})]
  [(uliftSheafFunctor.{s, t} J).PreservesInjectiveObjects]
  [HasExt.{w₁} (Sheaf J AddCommGrpCat.{t})] [HasExt.{w₂} (Sheaf J AddCommGrpCat.{max t s})]

/-- **The universe lift of abelian sheaves is bijective on `Ext`**, given enough injectives in the
smaller sheaf category and preservation of injective objects by the lift. It is exact and fully
faithful, so this is `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`. -/
theorem bijective_mapExtAddHom_uliftSheafFunctor (X Y : Sheaf J AddCommGrpCat.{t}) (n : ℕ) :
    letI := preservesFiniteColimits_uliftSheafFunctor.{s, t} J
    Function.Bijective ((uliftSheafFunctor.{s, t} J).mapExtAddHom.{w₁, w₂} X Y n) :=
  let := preservesFiniteColimits_uliftSheafFunctor.{s, t} J
  have : (uliftSheafFunctor.{s, t} J).Full := (fullyFaithfulUliftSheafFunctor.{s, t} J).full
  have : (uliftSheafFunctor.{s, t} J).Faithful :=
    (fullyFaithfulUliftSheafFunctor.{s, t} J).faithful
  (uliftSheafFunctor.{s, t} J).mapExt_bijective_of_preservesInjectiveObjects X Y n

/-- **Sheaf cohomology does not depend on the coefficient universe**: the cohomology of an
abelian sheaf `F` agrees in every degree with that of its universe lift,

  `H ^ n (C, F) ≃+ H ^ n (C, F ⋙ uliftFunctor)`,

given enough injectives in the smaller sheaf category and preservation of injective objects by
the lift. The two `Ext` universes are arbitrary.

The map is the universe lift on `Ext` out of the constant sheaf `ℤ`
(`Stacks.Sheaves.UniverseLift.bijective_mapExtAddHom_uliftSheafFunctor`), followed by
precomposition with the identification of the lift of the constant sheaf `ℤ` with the constant
sheaf `ℤ` (`Stacks.Sheaves.UniverseLift.uliftSheafFunctorConstantIntIso`). -/
def sheafHUliftAddEquiv (F : Sheaf J AddCommGrpCat.{t}) (n : ℕ) :
    Sheaf.H.{w₁} F n ≃+ Sheaf.H.{w₂} ((uliftSheafFunctor.{s, t} J).obj F) n :=
  letI := preservesFiniteColimits_uliftSheafFunctor.{s, t} J
  (AddEquiv.ofBijective _ (bijective_mapExtAddHom_uliftSheafFunctor.{w₁, w₂} J _ F n)).trans
    (((extFunctor.{w₂} n).mapIso (uliftSheafFunctorConstantIntIso.{s, t} J).symm.op).app
      ((uliftSheafFunctor.{s, t} J).obj F)).addCommGroupIsoToAddEquiv

/-- `sheafHUliftAddEquiv` on a class: the universe lift of the class, precomposed with the
identification of the lift of the constant sheaf `ℤ` with the constant sheaf `ℤ`. -/
theorem sheafHUliftAddEquiv_apply (F : Sheaf J AddCommGrpCat.{t}) (n : ℕ)
    (x : Sheaf.H.{w₁} F n) :
    letI := preservesFiniteColimits_uliftSheafFunctor.{s, t} J
    sheafHUliftAddEquiv.{w₁, w₂} J F n x =
      (Ext.mk₀ (uliftSheafFunctorConstantIntIso.{s, t} J).inv).comp
        (x.mapExactFunctor (uliftSheafFunctor.{s, t} J)) (zero_add n) :=
  rfl

/-- **`sheafHUliftAddEquiv` is natural in the sheaf**: it intertwines `H ^ n` of a morphism with
`H ^ n` of its universe lift. -/
theorem sheafHUliftAddEquiv_naturality {F G : Sheaf J AddCommGrpCat.{t}} (ψ : F ⟶ G) (n : ℕ)
    (x : Sheaf.H.{w₁} F n) :
    sheafHUliftAddEquiv.{w₁, w₂} J G n (Sheaf.H.map ψ n x) =
      Sheaf.H.map ((uliftSheafFunctor.{s, t} J).map ψ) n
        (sheafHUliftAddEquiv.{w₁, w₂} J F n x) := by
  let _ := preservesFiniteColimits_uliftSheafFunctor.{s, t} J
  rw [sheafHUliftAddEquiv_apply, sheafHUliftAddEquiv_apply, Sheaf.H.map_apply, Sheaf.H.map_apply,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- **Vanishing of cohomology does not depend on the coefficient universe.** -/
theorem subsingleton_sheafH_uliftSheafFunctor_iff (F : Sheaf J AddCommGrpCat.{t}) (n : ℕ) :
    Subsingleton (Sheaf.H.{w₂} ((uliftSheafFunctor.{s, t} J).obj F) n) ↔
      Subsingleton (Sheaf.H.{w₁} F n) :=
  (sheafHUliftAddEquiv.{w₁, w₂} J F n).toEquiv.subsingleton_congr.symm

end Stacks.Sheaves.UniverseLift

end
