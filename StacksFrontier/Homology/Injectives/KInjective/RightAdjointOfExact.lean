module

public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FlatPushforwardPreservesKInjectives

/-!
# A right adjoint of an exact functor preserves K-injective complexes

[Stacks, Tag 070G] says that if `v ⊣ u` with `v` exact, then `u`, applied degreewise, carries
K-injective complexes to K-injective complexes. The repository has that statement, as
`rightAdjoint_preserves_isKInjective`, in the module
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FlatPushforwardPreservesKInjectives`,
but phrased with the local predicate `IsKInjectiveHomotopyCategory` -- every morphism *in the
homotopy category* out of an acyclic complex is zero -- rather than with Mathlib's class
`CochainComplex.IsKInjective`, which asks that every *chain map* out of an acyclic complex be
null-homotopic. This file identifies the two and restates the tag as an instance-friendly
statement about the class, and specialises it to an exact equivalence.

The identification is formal: `HomotopyCategory.quotient` is full, so every morphism of the
homotopy category is the image of a chain map, and `HomotopyCategory.quotient_map_eq_zero_iff`
says that image vanishes exactly when the chain map is null-homotopic.

The specialisation to an equivalence is what makes the statement usable for transporting the
cohomology theory of a ringed site to abelian sheaves along
`Stacks.Cohomology.ZModSheaf.toSheaf_isEquivalence`: an equivalence is a right adjoint of its own
inverse, and the inverse of an exact equivalence is exact.

## Main results

* `Stacks.Injectives.isKInjectiveHomotopyCategory_iff_isKInjective`: the two formulations of
  K-injectivity agree.
* `Stacks.Injectives.isKInjective_mapHomologicalComplex_of_adjunction`: **Tag 070G** for
  Mathlib's class.
* `Stacks.Injectives.isKInjective_mapHomologicalComplex_of_isEquivalence`: an exact equivalence,
  applied degreewise, preserves K-injective complexes.

## Implementation notes

The two abelian categories share their universes in the first two statements, as they do in
`rightAdjoint_preserves_isKInjective`, which those statements go through. The specialisation to
an equivalence does not go through it -- it appeals to the adjoint criterion
`CochainComplex.isKInjective_mapHomologicalComplex_of_exact` directly -- and is therefore stated
at independent universes, which is what a transport along an equivalence of categories built on
different universes needs.

## References

* [Stacks Project, Tag 070G](https://stacks.math.columbia.edu/tag/070G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u v₁ v₂ u₁ u₂

namespace Stacks.Injectives

variable {A : Type u} [Category.{v} A] [Abelian A] {B : Type u} [Category.{v} B] [Abelian B]

/-- The `Hom`-vanishing formulation of K-injectivity agrees with Mathlib's class: the quotient
onto the homotopy category is full, and a chain map becomes zero there exactly when it is
null-homotopic. -/
public lemma isKInjectiveHomotopyCategory_iff_isKInjective (I : CochainComplex A ℤ) :
    IsKInjectiveHomotopyCategory I ↔ I.IsKInjective := by
  refine ⟨fun h ↦ ⟨fun {M} f hM ↦ (HomotopyCategory.quotient_map_eq_zero_iff f).1
    (h M hM ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f))⟩, fun h M hM f ↦ ?_⟩
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_surjective f
  exact (HomotopyCategory.quotient_map_eq_zero_iff g).2 (h.nonempty_homotopy_zero g hM)

/-- **Stacks Project, Tag 070G.** A right adjoint of an exact functor, applied degreewise,
carries a K-injective complex to a K-injective complex. -/
public lemma isKInjective_mapHomologicalComplex_of_adjunction
    (u : A ⥤ B) (v : B ⥤ A) [u.Additive] [v.Additive] (adj : v ⊣ u)
    [PreservesFiniteLimits v] [PreservesFiniteColimits v]
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (isKInjectiveHomotopyCategory_iff_isKInjective _).1
    (rightAdjoint_preserves_isKInjective u v adj I
      ((isKInjectiveHomotopyCategory_iff_isKInjective I).2 inferInstance))

/-- **An exact equivalence, applied degreewise, preserves K-injective complexes**: it is a right
adjoint of its own inverse, which is again exact.

The two categories carry independent universes here, unlike in the two statements above: the
adjoint criterion `CochainComplex.isKInjective_mapHomologicalComplex_of_exact` that this appeals
to is stated at independent universes, and a consumer transporting a derived functor along an
equivalence has no reason for the two to agree. -/
public lemma isKInjective_mapHomologicalComplex_of_isEquivalence {A : Type u₁} [Category.{v₁} A]
    [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B] (u : A ⥤ B) [u.IsEquivalence]
    [u.Additive] (I : CochainComplex A ℤ) [I.IsKInjective] :
    CochainComplex.IsKInjective ((u.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  have : (u.inv).Additive := Functor.additive_of_preserves_binary_products _
  exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact u u.inv
    u.asEquivalence.symm.toAdjunction I

end Stacks.Injectives

end
