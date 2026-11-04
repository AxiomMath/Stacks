module

public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.UniverseLiftFullyFaithful

/-!
# The universe lift of sheaves of modules is exact

`SheafOfModules.uliftFunctor` replaces the sections of a sheaf of modules by their universe
lift.  This file shows that it is an exact functor between the abelian categories of sheaves of
modules in the two universes: it is additive, it preserves finite limits and it preserves
finite colimits, hence it preserves homology.

## Main results

* `SheafOfModules.uliftFunctor_additive`: the universe lift is additive.
* `SheafOfModules.uliftFunctor_preservesFiniteLimits`: it preserves finite limits.
* `SheafOfModules.uliftFunctor_preservesEpimorphisms`: it preserves epimorphisms.
* `SheafOfModules.uliftFunctor_preservesFiniteColimits`: it preserves finite colimits.
* `SheafOfModules.uliftFunctor_preservesHomology`: it preserves homology.

## Implementation notes

Composed with the forgetful functor to abelian sheaves and then to abelian presheaves, the
universe lift is, definitionally, the forgetful functor followed by postcomposition with
`AddCommGrpCat.uliftFunctor`, which preserves finite limits sectionwise.  The forgetful functor
reflects isomorphisms and preserves finite limits, so it reflects them, and left exactness of the
lift follows.

Epimorphisms of sheaves of modules are the morphisms that are locally surjective on underlying
abelian presheaves (`Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective`), and the
universe lift does not change local surjectivity because `ULift.up` is a bijection on sections
(`CategoryTheory.Presheaf.isLocallySurjective_whiskerRight_uliftFunctor`).  An additive functor
between abelian categories which is left exact and preserves epimorphisms carries short exact
sequences to short exact sequences, hence is right exact as well.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v₁ u₁ w z t

namespace SheafOfModules

section ULift

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{w})

/-- The universe lift of sheaves of modules is additive. -/
instance uliftFunctor_additive : (uliftFunctor.{v₁, u₁, w, z, t} (R := R)).Additive where
  map_add := by
    intros
    rfl

variable [HasSheafify J AddCommGrpCat.{z}] [J.WEqualsLocallyBijective AddCommGrpCat.{z}]
  [HasSheafify J AddCommGrpCat.{max z t}] [J.WEqualsLocallyBijective AddCommGrpCat.{max z t}]

/-- **The universe lift of sheaves of modules preserves finite limits.** After forgetting to
abelian presheaves it is postcomposition with `AddCommGrpCat.uliftFunctor`, and the forgetful
functor reflects the finite limits it preserves. -/
instance uliftFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (uliftFunctor.{v₁, u₁, w, z, t} (R := R)) := by
  let G := toSheaf.{max z t} R ⋙ sheafToPresheaf J AddCommGrpCat.{max z t}
  have : G.ReflectsIsomorphisms := by
    have : (toSheaf.{max z t} R).ReflectsIsomorphisms := inferInstance
    exact reflectsIsomorphisms_comp _ _
  have : ReflectsFiniteLimits G := ⟨fun K _ _ ↦ reflectsLimitsOfShape_of_reflectsIsomorphisms⟩
  have : PreservesFiniteLimits (uliftFunctor.{v₁, u₁, w, z, t} (R := R) ⋙ G) := by
    change PreservesFiniteLimits ((toSheaf.{z} R ⋙ sheafToPresheaf J AddCommGrpCat.{z}) ⋙
      (Functor.whiskeringRight Cᵒᵖ _ _).obj AddCommGrpCat.uliftFunctor.{t, z})
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _ G

/-- **The universe lift of sheaves of modules preserves epimorphisms**: an epimorphism is locally
surjective on sections, and lifting the universe of the sections does not change that. -/
instance uliftFunctor_preservesEpimorphisms :
    (uliftFunctor.{v₁, u₁, w, z, t} (R := R)).PreservesEpimorphisms where
  preserves {M N} f hf := by
    have h : Presheaf.IsLocallySurjective J
        ((PresheafOfModules.toPresheaf R.obj).map f.val) :=
      (Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective f).1 hf
    rw [Stacks.SheafOfModules.EpiMono.epi_iff_isLocallySurjective]
    exact inferInstanceAs (Presheaf.IsLocallySurjective J (Functor.whiskerRight
      ((PresheafOfModules.toPresheaf R.obj).map f.val) AddCommGrpCat.uliftFunctor.{t}))

/-- **The universe lift of sheaves of modules preserves finite colimits.** It is left exact and
preserves epimorphisms, so it carries short exact sequences to short exact sequences. -/
instance uliftFunctor_preservesFiniteColimits :
    PreservesFiniteColimits (uliftFunctor.{v₁, u₁, w, z, t} (R := R)) := by
  have h₀ : PreservesFiniteLimits (uliftFunctor.{v₁, u₁, w, z, t} (R := R)) := inferInstance
  have hL : ∀ S : ShortComplex (SheafOfModules.{z} R), S.ShortExact →
      (S.map (uliftFunctor.{v₁, u₁, w, z, t} (R := R))).Exact ∧
        Mono ((uliftFunctor.{v₁, u₁, w, z, t} (R := R)).map S.f) :=
    ((Functor.preservesFiniteLimits_tfae
      (uliftFunctor.{v₁, u₁, w, z, t} (R := R))).out 1 4).2 h₀
  have hR : ∀ S : ShortComplex (SheafOfModules.{z} R), S.ShortExact →
      (S.map (uliftFunctor.{v₁, u₁, w, z, t} (R := R))).Exact ∧
        Epi ((uliftFunctor.{v₁, u₁, w, z, t} (R := R)).map S.g) := fun S hS ↦ by
    have := hS.epi_g
    exact ⟨(hL S hS).1, inferInstance⟩
  exact ((Functor.preservesFiniteColimits_tfae
    (uliftFunctor.{v₁, u₁, w, z, t} (R := R))).out 1 4).1 hR

/-- **The universe lift of sheaves of modules preserves homology**, being exact. -/
instance uliftFunctor_preservesHomology :
    (uliftFunctor.{v₁, u₁, w, z, t} (R := R)).PreservesHomology :=
  Functor.preservesHomologyOfExact _

end ULift

end SheafOfModules

end
