module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.MorPresheaf
import StacksCore.Tactic.StacksAttribute

/-!
# Descent data relative to a sieve

This is the sieve-indexed form of the descent data of Stacks 026B, in the shape that Mathlib gives
them for a pseudofunctor, `CategoryTheory.Pseudofunctor.DescentData`: a family of objects, gluing
isomorphisms between their pullbacks over every object of the base mapping compatibly into two of
the sources, and two conditions on those isomorphisms — compatibility with composition, which is
the cocycle condition, and compatibility with base change.

Both conditions are equations between morphisms of one fibre, with no comparison isomorphism
quantified over, and that is only possible because the isomorphisms are taken between the *chosen*
pullbacks of `CategoryTheory.Functor.IsPreFibered`: two gluing isomorphisms sharing a middle arrow
then have literally the same object in the middle, so they compose on the nose, exactly as
`CategoryTheory.Pseudofunctor.DescentData.hom_comp` does for the pullback functors of a
pseudofunctor. Stating the cocycle condition between *arbitrary* cartesian lifts instead forces
comparison isomorphisms into it, and quantifying those existentially makes the condition vacuous:
the equation can then be solved for one of them.

Base change (`CategoryTheory.Functor.SieveDescentDatum.iso_pullback`, Mathlib's
`CategoryTheory.Pseudofunctor.DescentData.pullHom_hom`) is a genuinely separate condition: the
cocycle condition relates gluing isomorphisms over one and the same object `Z` of the base only, so
without it the isomorphisms over different `Z` are unrelated, and a family that is a coboundary for
a non-natural choice of fibre automorphisms would satisfy the cocycle condition while descending to
nothing. It is what makes the sieve-indexed data agree with the data of Stacks 026B over the fibre
products `Uᵢ ×_U Uⱼ`, of which the isomorphisms over a general `Z` are the base changes.

## Main definitions

* `CategoryTheory.Functor.SieveDescentDatum`, a descent datum relative to a sieve, Stacks 026B;
* `CategoryTheory.Functor.SieveDescentDatum.IsEffective` and
  `CategoryTheory.Functor.HasEffectiveDescent`, condition (3) of Stacks 026F.
-/

@[expose] public section

namespace CategoryTheory

open Limits Opposite

universe v₁ v₂ u₁ u₂

namespace Functor

variable {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂} [Category.{v₂} 𝒳]

/-- A descent datum relative to a sieve `R` on `U`: an object of the fibre over `V` for each arrow
`f : V ⟶ U` of `R`, and for each pair of arrows of `R` and each pair of morphisms `ε`, `ε'` into
their sources agreeing over `U`, an isomorphism between the chosen pullbacks along `ε` and `ε'` of
the two attached objects, compatible with composition and with base change. -/
@[stacks_fixed 026B "(1), sieve-indexed, with no chosen fibre products `U i ×_U U j`",
  sga "3 IV 2.1" "descent datum", sga "4½ Arcata 1.4.4"]
structure SieveDescentDatum (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U : 𝒮} (R : Sieve U) where
  /-- The object over the source of an arrow of `R`. -/
  obj : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U), R f → p.Fiber V
  /-- The gluing isomorphism between the two chosen pullbacks. -/
  iso :
    ∀ ⦃V W Z : 𝒮⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
      (ε : Z ⟶ V) (ε' : Z ⟶ W) (_heq : ε ≫ f = ε' ≫ g),
        pullbackFiber p (obj f hf) ε ≅ pullbackFiber p (obj g hg) ε'
  /-- The cocycle condition: the gluing isomorphisms of a triple of arrows of `R`, taken over one
  and the same object `Z` of the base, compose. -/
  cocycle :
    ∀ ⦃V W X Z : 𝒮⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
      ⦃h : X ⟶ U⦄ (hh : R h)
      (ε₁ : Z ⟶ V) (ε₂ : Z ⟶ W) (ε₃ : Z ⟶ X)
      (h₁₂ : ε₁ ≫ f = ε₂ ≫ g) (h₂₃ : ε₂ ≫ g = ε₃ ≫ h)
      (h₁₃ : ε₁ ≫ f = ε₃ ≫ h),
      (iso hf hg ε₁ ε₂ h₁₂).hom ≫ (iso hg hh ε₂ ε₃ h₂₃).hom = (iso hf hh ε₁ ε₃ h₁₃).hom
  /-- Compatibility with base change: the gluing isomorphism over `Z'` at `γ ≫ ε` and `γ ≫ ε'` is
  the base change along `γ` of the one over `Z` at `ε` and `ε'`. -/
  iso_pullback :
    ∀ ⦃V W Z Z' : 𝒮⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
      (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) (γ : Z' ⟶ Z),
      (pullbackFiberCompIso (obj f hf) ε γ).inv ≫
          (pullbackFiberIso (iso hf hg ε ε' heq) γ).hom ≫
          (pullbackFiberCompIso (obj g hg) ε' γ).hom =
        (iso hf hg (γ ≫ ε) (γ ≫ ε')
          (by rw [Category.assoc, Category.assoc, heq])).hom

namespace SieveDescentDatum

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U : 𝒮} {R : Sieve U} (D : SieveDescentDatum p R)

/-- The gluing isomorphism of an arrow of `R` with itself along one and the same morphism into its
source is the identity. Under the vacuous form of the cocycle condition this was not a consequence
of the datum at all, and had to be extracted from effectiveness. -/
@[simp]
lemma iso_self ⦃V Z : 𝒮⦄ ⦃f : V ⟶ U⦄ (hf : R f) (ε : Z ⟶ V) (heq : ε ≫ f = ε ≫ f) :
    (D.iso hf hf ε ε heq).hom = 𝟙 _ := by
  have h := D.cocycle hf hf hf ε ε ε heq heq heq
  rw [← cancel_mono (D.iso hf hf ε ε heq).hom]
  simpa using h

/-- The two gluing isomorphisms of a pair of arrows of `R` are inverse to each other. -/
lemma iso_symm ⦃V W Z : 𝒮⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
    (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g) :
    (D.iso hg hf ε' ε heq.symm).hom = (D.iso hf hg ε ε' heq).inv := by
  rw [← cancel_epi (D.iso hf hg ε ε' heq).hom, Iso.hom_inv_id,
    D.cocycle hf hg hf ε ε' ε heq heq.symm rfl, D.iso_self]

/-- A descent datum is effective when it comes from an object `x` of the fibre over `U`: there is a
cartesian morphism from each of its objects to `x`, compatibly with the gluing isomorphisms. -/
@[stacks 026E "(3), effectivity of a descent datum, stated as the existence of an object `x` of the
  fibre over `U` and a cartesian morphism from each object of the datum to `x` compatible with the
  gluing isomorphisms, in place of an isomorphism with `(f_i^* X, can)`.", sga "3 IV 3.5.1"]
def IsEffective : Prop :=
  ∃ (x : p.Fiber U)
    (ζ : ∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R f), (D.obj f hf).1 ⟶ x.1),
    (∀ ⦃V : 𝒮⦄ (f : V ⟶ U) (hf : R f), p.IsCartesian f (ζ f hf)) ∧
    (∀ ⦃V W Z : 𝒮⦄ ⦃f : V ⟶ U⦄ (hf : R f) ⦃g : W ⟶ U⦄ (hg : R g)
       (ε : Z ⟶ V) (ε' : Z ⟶ W) (heq : ε ≫ f = ε' ≫ g),
       Fiber.fiberInclusion.map (D.iso hf hg ε ε' heq).hom ≫
           IsPreFibered.pullbackMap (D.obj g hg).2 ε' ≫ ζ g hg =
         IsPreFibered.pullbackMap (D.obj f hf).2 ε ≫ ζ f hf)

end SieveDescentDatum

/-- Every descent datum relative to a covering sieve is effective. -/
def HasEffectiveDescent (p : 𝒳 ⥤ 𝒮) [p.IsFibered] (J : GrothendieckTopology 𝒮) : Prop :=
  ∀ ⦃U : 𝒮⦄ (R : Sieve U), R ∈ J U → ∀ (D : SieveDescentDatum p R), D.IsEffective

end Functor

end CategoryTheory
