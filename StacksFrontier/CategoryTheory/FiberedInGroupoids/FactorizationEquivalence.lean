module

public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Factorization

/-!
# The vertical iso-comma category is equivalent to its left factor over the base (Stacks 06N7)

Let `q : 𝒴 ⥤ 𝒞` and `F : 𝒳 ⥤ 𝒴`. The functor
`CategoryTheory.Functor.IsFiberedInGroupoids.Factorization.XPrime.fromLeft`, which sends an
object `x` of `𝒳` to the triple `(x, F x, refl)`, is an equivalence `𝒳 ≌ XPrime q F`, and it is
an equivalence over `𝒞` in the sense of `CategoryTheory.Functor.IsEquivalenceOver`.

This is clause (2) of Stacks 06N7, stated for the comparison functor itself rather than inside an
existential.

## Main definitions

* `CategoryTheory.Functor.IsFiberedInGroupoids.Factorization.XPrime.isEquivalenceOver`: the
  comparison functor is an equivalence over `𝒞`.
* `CategoryTheory.Functor.IsFiberedInGroupoids.Factorization.XPrime.equivalence`: the underlying
  equivalence of categories.

## References

* [Stacks Project, Tag 06N7](https://stacks.math.columbia.edu/tag/06N7)
-/

@[expose] public section

namespace CategoryTheory.Functor.IsFiberedInGroupoids.Factorization

universe u₁ v₁ u₂ v₂ u₃ v₃

variable {𝒞 : Type u₂} [Category.{v₂} 𝒞] {𝒳 : Type u₁} [Category.{v₁} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] (p : 𝒳 ⥤ 𝒞) (q : 𝒴 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒴)

/-- The comparison functor `𝒳 ⥤ XPrime q F` is an equivalence over `𝒞`: its quasi-inverse
`XPrime.projLeft` commutes strictly with the structure functors, and the unit and counit
isomorphisms are vertical. -/
def XPrime.isEquivalenceOver :
    IsEquivalenceOver p (XPrime.structureFunctor p q F) (XPrime.fromLeft q F) where
  inv := XPrime.projLeft q F
  inv_over := XPrime.projLeft_comp_eq p q F
  unitIso := eqToIso (XPrime.fromLeft_comp_projLeft q F)
  counitIso := XPrime.counitIso q F
  unit_vertical := by
    intro A
    refine (IsHomLift.id_iff_exists_eqToHom p _).2 ⟨rfl, ?_⟩
    rw [eqToIso.hom, eqToHom_app, eqToHom_map]
  counit_vertical := by
    intro A
    refine (IsHomLift.id_iff_exists_eqToHom (XPrime.structureFunctor p q F) _).2 ⟨rfl, ?_⟩
    simp [XPrime.counitIso, XPrime.structureFunctor, XPrime.fromLeft, XPrime.projLeft]

/-- The equivalence of categories `𝒳 ≌ XPrime q F` given by the comparison functor
`XPrime.fromLeft` and the projection `XPrime.projLeft`. -/
def XPrime.equivalence : 𝒳 ≌ XPrime q F :=
  .mk (XPrime.fromLeft q F) (XPrime.projLeft q F)
    (eqToIso (XPrime.fromLeft_comp_projLeft q F).symm) (XPrime.counitIso q F)

/-- The functor of `XPrime.equivalence q F` is `XPrime.fromLeft q F`. -/
@[simp]
lemma XPrime.equivalence_functor : (XPrime.equivalence q F).functor = XPrime.fromLeft q F := rfl

/-- The inverse of `XPrime.equivalence q F` is `XPrime.projLeft q F`. -/
@[simp]
lemma XPrime.equivalence_inverse : (XPrime.equivalence q F).inverse = XPrime.projLeft q F := rfl

end CategoryTheory.Functor.IsFiberedInGroupoids.Factorization
