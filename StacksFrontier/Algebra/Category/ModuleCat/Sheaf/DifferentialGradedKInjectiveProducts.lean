module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedKInjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedProductHomotopy
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedProducts

/-!
# Products of K-injective differential graded modules

Let `R` be a sheaf of rings on a site and let `A` be a sheaf of differential graded
`R`-algebras. A product of K-injective right differential graded `A`-modules is K-injective.

## Main results

* `SheafOfModules.DifferentialGradedModule.isKInjective_pi`: a product of K-injective right
  differential graded modules is K-injective.

## Implementation notes

K-injectivity is a condition on morphism groups in the homotopy category, so the proof needs
the image of a product fan under the quotient functor to be a product there. The existence half
of that universal property uses only that the quotient functor is full; its uniqueness half is
`SheafOfModules.DifferentialGradedModule.homotopyIntoProduct`, which assembles a homotopy into
a product out of homotopies into its factors. With the product fan in hand, two morphisms into
a product of K-injectives agree after every projection — there being at most one morphism into
each factor — and hence agree.

The base is an arbitrary sheaf of rings on an arbitrary site rather than the structure sheaf of
a ringed site, and the universes of the site, the ring and the algebra pieces are independent;
a ringed site `X` is the case `R := X.ringSheaf`.

## References

* [Stacks Project, Tag 0FSV](https://stacks.math.columbia.edu/tag/0FSV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe t a m v u

namespace SheafOfModules

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{t}}

/-- The image of a product fan of right differential graded modules under the quotient functor
is a product in the homotopy category. -/
private noncomputable def isLimitQuotientProductFan
    {A : DifferentialGradedAlgebra.{t, a} R} {T : Type m}
    (I : T → DifferentialGradedModule.{t, a, m} A) :
    IsLimit (Fan.mk ((HomotopyCategory.quotient A).obj (∏ᶜ I))
      (fun s => (HomotopyCategory.quotient A).map (Pi.π I s))) := by
  let q : DifferentialGradedModule.{t, a, m} A ⥤ HomotopyCategory.{t, a, m} A :=
    HomotopyCategory.quotient A
  letI : q.Full := HomotopyCategory.quotient_full A
  refine Fan.IsLimit.mk _ (fun s => q.map (Pi.lift fun i => q.preimage (s.proj i))) ?_ ?_
  · intro s i
    change q.map (Pi.lift fun j => q.preimage (s.proj j)) ≫ q.map (Pi.π I i) = s.proj i
    rw [← Functor.map_comp, Pi.lift_π, Functor.map_preimage]
  · intro s m hm
    have hm' : q.map (q.preimage m) = m := Functor.map_preimage _ _
    rw [← hm']
    refine (HomotopyCategory.quotient_map_eq_iff
      (q.preimage m) (Pi.lift fun i => q.preimage (s.proj i))).2
      ⟨homotopyIntoProduct I (∏ᶜ I) (Pi.π I) (productIsProduct I) (fun i => ?_)⟩
    have ht : q.map ((q.preimage m) ≫ Pi.π I i) =
        q.map ((Pi.lift fun j => q.preimage (s.proj j)) ≫ Pi.π I i) := by
      rw [Functor.map_comp]
      calc
        q.map (q.preimage m) ≫ q.map (Pi.π I i) = m ≫ q.map (Pi.π I i) := by rw [hm']
        _ = s.proj i := hm i
        _ = q.map ((Pi.lift fun j => q.preimage (s.proj j)) ≫ Pi.π I i) := by
          rw [Pi.lift_π, Functor.map_preimage]
    exact (HomotopyCategory.quotient_map_eq_iff
      (q.preimage m ≫ Pi.π I i)
      ((Pi.lift fun j => q.preimage (s.proj j)) ≫ Pi.π I i)).mp ht

/-- A product of K-injective right differential graded modules is K-injective. -/
@[stacks 0FSV]
theorem isKInjective_pi {A : DifferentialGradedAlgebra.{t, a} R} {T : Type m}
    (I : T → DifferentialGradedModule.{t, a, m} A) (hI : ∀ s, IsKInjective (I s)) :
    IsKInjective (∏ᶜ I) := by
  intro M hM
  refine ⟨fun f g => (isLimitQuotientProductFan I).hom_ext ?_⟩
  intro ⟨s⟩
  exact (hI s M hM).elim _ _

end DifferentialGradedModule

end SheafOfModules
