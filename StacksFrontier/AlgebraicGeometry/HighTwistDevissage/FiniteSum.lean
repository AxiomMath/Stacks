module

public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts

/-!
# An additive functor kills a finite direct sum of objects it kills

The cohomological arguments of Chapter 30 all pass through a short exact sequence whose middle
term is a *finite* direct sum of twists of one invertible sheaf, and the hypothesis available is
the vanishing of the cohomology of each twist separately. This file supplies the step that turns
one into the other: an additive functor between preadditive categories sends a finite biproduct
to the biproduct of the images, and a finite biproduct of zero objects is a zero object.

Nothing here is about sheaves, schemes or cohomology, and nothing is assumed beyond additivity;
the finiteness of the index type is essential, since an additive functor need not preserve
infinite direct sums.

## Main results

* `Stacks.HighTwistDevissage.isZero_biproduct`: a finite biproduct of zero objects is zero.
* `Stacks.HighTwistDevissage.isZero_obj_biproduct`: an additive functor sends a finite biproduct
  of objects it sends to zero to a zero object.
* `Stacks.HighTwistDevissage.isZero_obj_of_isBilimit`: the same for an arbitrary bicone
  exhibiting an object as a finite direct sum. **This is the form to use.**

## Implementation notes

`isZero_biproduct` is proved from `CategoryTheory.Limits.biproduct.total`, which writes the
identity of `⨁ f` as the sum of the `πᵢ ≫ ιᵢ`: each summand factors through `f i`, which is zero,
so the identity is zero, which is `CategoryTheory.Limits.IsZero.iff_id_eq_zero`. The route
through `IsZero.iff_id_eq_zero` avoids having to produce a zero object of the ambient category,
which is not assumed. `CategoryTheory.Limits.PreservesBiproduct` is found by instance search from
`CategoryTheory.Functor.Additive`, so `CategoryTheory.Functor.mapBiproduct` applies with no
further hypothesis.

**Why `isZero_obj_of_isBilimit` is the usable form, and `⨁`/`∐` are not.** `HasBiproduct` and
`HasCoproduct` are data-carrying classes, so `⨁ f` and `∐ f` are *terms depending on a chosen
instance*. A lemma stated about `⨁ f` with the instance as a hypothesis does apply to a goal
mentioning `⨁ f`, since the hypothesis is a metavariable unification can assign. But a lemma
stated about `∐ f` where the coproduct instance is *derived* from a `HasBiproduct` hypothesis is
useless against a goal whose `∐ f` came from the ambient `HasCoproduct`: the two instance terms
are propositionally but not definitionally equal, so unification fails and the instance cannot be
assigned. Stated that way, the coproduct form fails with
`failed to synthesize instance HasBiproduct f` at the call site,
`Stacks.HighTwistDevissage.isZero_hgroup_directSum_tensorPowModule`, with the family right there
in the goal. `Bicone` together with `Bicone.IsBilimit` carries no instance at all, and
`CategoryTheory.Limits.biproduct.bicone` with `CategoryTheory.Limits.biproduct.isBilimit` supplies
it from any `HasBiproduct`, so the bilimit form is strictly more applicable and never has this
problem.

No tag attribute is attached: this is a general categorical step and the statement of no tag.
-/

@[expose] public section

universe v v' u u'

namespace Stacks.HighTwistDevissage

open CategoryTheory CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [Preadditive C] {D : Type u'} [Category.{v'} D]
  [Preadditive D]

/-- A finite biproduct of zero objects is a zero object. -/
theorem isZero_biproduct {ι : Type} [Finite ι] (f : ι → C) [HasBiproduct f]
    (h : ∀ i, IsZero (f i)) : IsZero (⨁ f) := by
  have := Fintype.ofFinite ι
  rw [IsZero.iff_id_eq_zero, ← biproduct.total]
  exact Finset.sum_eq_zero fun i _ => by
    rw [(h i).eq_zero_of_tgt (biproduct.π f i), zero_comp]

/-- An additive functor sends a finite biproduct of objects it sends to zero to a zero object. -/
theorem isZero_obj_biproduct (F : C ⥤ D) [F.Additive] {ι : Type} [Finite ι] (f : ι → C)
    [HasBiproduct f] [HasBiproduct fun i => F.obj (f i)] (h : ∀ i, IsZero (F.obj (f i))) :
    IsZero (F.obj (⨁ f)) :=
  IsZero.of_iso (isZero_biproduct (fun i => F.obj (f i)) h) (F.mapBiproduct f)

/-- **An additive functor sends a finite direct sum of objects it sends to zero to a zero
object.** The direct sum is given by an arbitrary bicone exhibiting `b.pt` as the biproduct of
`f`, so the statement mentions no `HasBiproduct` instance and applies to any object presented as
a finite direct sum. -/
theorem isZero_obj_of_isBilimit (F : C ⥤ D) [F.Additive] {ι : Type} [Finite ι] {f : ι → C}
    {b : Bicone f} (hb : b.IsBilimit) (hD : HasBiproduct fun i => F.obj (f i))
    (h : ∀ i, IsZero (F.obj (f i))) : IsZero (F.obj b.pt) :=
  have : HasBiproduct f := HasBiproduct.mk ⟨b, hb⟩
  IsZero.of_iso (isZero_obj_biproduct F f h) (F.mapIso (biproduct.uniqueUpToIso f hb))

end Stacks.HighTwistDevissage

end
