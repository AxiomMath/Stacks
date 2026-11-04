module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.Deformation.Artin.Versality.OpennessCounterexampleAxioms

/-!
# The comparison at a square of fibres for a category fibred in setoids

`Deformation.Artin.fiberSquareComparison` compares the fibre of a fibred category over the
fourth corner `Z` of a commutative square `f ≫ i = g ≫ j` with the two-fibre product of the
fibres over the two middle corners `V` and `W`. For a faithful structure functor — a category
fibred in setoids — the comparison is an equivalence as soon as two conditions on arrows lying
over the edges of the square hold: objects over `V` and `W` with a common restriction to `U`
receive arrows into a common object over `Z`, and two objects over `Z` whose restrictions to `V`
and to `W` agree are isomorphic.

## Main results

* `Deformation.Artin.FiberSquare.isEquivalence_of_faithful`: the comparison for a category
  fibred in setoids is an equivalence under the two arrow conditions.

## Implementation notes

The essential surjectivity is obtained through the canonical isomorphisms between two cartesian
lifts (`CategoryTheory.Functor.fiberIsoOfCartesian`); the choice of pullbacks is arbitrary.
The readings of full faithfulness of the comparison on arrows, for a category fibred in
groupoids, are `Deformation.Artin.fiberSquareComparison_arrow_ext` and
`Deformation.Artin.fiberSquareComparison_pointed_arrow_exists` in
`StacksFrontier/Deformation/Artin/ChangeOfField/Equivalence.lean`.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin.FiberSquare

open CategoryTheory.Functor

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Limits.CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoryTheory.Limits.CategoricalPullback.π₁
  CategoryTheory.Limits.CategoricalPullback.π₂

variable {C : Type*} [Category C] {Y : Type*} [Category Y]
variable (q : Y ⥤ C) (c : q.ChoiceOfPullbacks)
variable {U V W Z : C} (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
variable (w : f ≫ i = g ≫ j)

/-- **The comparison for a category fibred in setoids.** Let `q` be fibred in groupoids and
faithful. The comparison at a commutative square is an equivalence as soon as (gluing) any two
arrows out of an object over `U`, over `f` and over `g`, are followed by arrows over `i` and `j`
into a common object over `Z`, and (separation) two objects over `Z` receiving arrows over `i`
from a common object and arrows over `j` from a common object are isomorphic in the fibre. -/
theorem isEquivalence_of_faithful (hq : q.IsFiberedInGroupoids) [q.Faithful]
    (hglue : ∀ (x : q.Fiber U) (y : q.Fiber V) (z : q.Fiber W) (α : x.1 ⟶ y.1)
      (β : x.1 ⟶ z.1), q.IsHomLift f α → q.IsHomLift g β →
      ∃ (t : q.Fiber Z) (γ : y.1 ⟶ t.1) (δ : z.1 ⟶ t.1), q.IsHomLift i γ ∧ q.IsHomLift j δ)
    (hsep : ∀ (s t : q.Fiber Z) (y : q.Fiber V) (z : q.Fiber W) (r : y.1 ⟶ s.1)
      (r' : y.1 ⟶ t.1) (s₂ : z.1 ⟶ s.1) (s₂' : z.1 ⟶ t.1), q.IsHomLift i r →
      q.IsHomLift i r' → q.IsHomLift j s₂ → q.IsHomLift j s₂' → Nonempty (s ⟶ t)) :
    (fiberSquareComparison q c f g i j w).IsEquivalence := by
  have hhom := fun {T : C} (a b : q.Fiber T) => subsingleton_fiber_hom_of_faithful q a b
  let F := fiberSquareComparison q c f g i j w
  have : F.Faithful := ⟨fun {a b} φ ψ _ => (hhom a b).elim φ ψ⟩
  have : F.Full := ⟨fun {s t} m => by
    have h1 : q.IsHomLift (𝟙 V) (Fiber.fiberInclusion.map m.fst) := m.fst.property
    have h2 : q.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map m.snd) := m.snd.property
    have hr' : q.IsHomLift i (Fiber.fiberInclusion.map m.fst ≫ c.map i t) :=
      CategoryTheory.IsHomLift.comp_lift_id_left' q V _ i (c.map i t)
    have hs' : q.IsHomLift j (Fiber.fiberInclusion.map m.snd ≫ c.map j t) :=
      CategoryTheory.IsHomLift.comp_lift_id_left' q W _ j (c.map j t)
    obtain ⟨γ⟩ := hsep s t (c.obj i s) (c.obj j s) (c.map i s) _ (c.map j s) _ inferInstance
      hr' inferInstance hs'
    exact ⟨γ, CategoricalPullback.hom_ext ((hhom _ _).elim _ _) ((hhom _ _).elim _ _)⟩⟩
  have : F.EssSurj := ⟨fun e => by
    have h₀ : q.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map e.iso.hom) := e.iso.hom.property
    have hβ : q.IsHomLift g (Fiber.fiberInclusion.map e.iso.hom ≫ c.map g e.snd) :=
      CategoryTheory.IsHomLift.comp_lift_id_left' q U _ g (c.map g e.snd)
    obtain ⟨t, γ, δ, hγ, hδ⟩ := hglue (c.obj f e.fst) e.fst e.snd (c.map f e.fst)
      (Fiber.fiberInclusion.map e.iso.hom ≫ c.map g e.snd) inferInstance hβ
    exact ⟨t, ⟨CategoricalPullback.mkIso
      (fiberIsoOfCartesian i (c.map i t) γ
        (hq.isStronglyCartesian_homLift i (c.map i t)).isCartesian_of_isStronglyCartesian
        (hq.isStronglyCartesian_homLift i γ).isCartesian_of_isStronglyCartesian)
      (fiberIsoOfCartesian j (c.map j t) δ
        (hq.isStronglyCartesian_homLift j (c.map j t)).isCartesian_of_isStronglyCartesian
        (hq.isStronglyCartesian_homLift j δ).isCartesian_of_isStronglyCartesian)
      ((hhom _ _).elim _ _)⟩⟩⟩
  exact { }

end Deformation.Artin.FiberSquare

end
