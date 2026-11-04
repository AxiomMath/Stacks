module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# The inverse of a braided equivalence is braided

Let `e : C ≌ D` be an equivalence of categories between braided monoidal categories whose
functor `e.functor` is braided monoidal. The monoidal structure transported to `e.inverse`
along the adjunction `e.functor ⊣ e.inverse` is then braided as well: the commutativity
constraint of `C` is carried to that of `D` by `e.functor`, and `e.functor` is faithful, so
the braiding identity for `e.inverse` can be checked after applying `e.functor`.

## Main results

* `CategoryTheory.Equivalence.isMonoidal_inverseMonoidal`: the adjunction underlying `e` is
  monoidal for the monoidal structure `Equivalence.inverseMonoidal` puts on `e.inverse`.
* `CategoryTheory.Equivalence.inverseCompFunctorLaxBraided`: the composite
  `e.inverse ⋙ e.functor` is lax braided, being monoidally isomorphic to `𝟭 D`.
* `CategoryTheory.Equivalence.inverseLaxBraided`: the inverse of a monoidal equivalence
  between braided categories is lax braided.
* `CategoryTheory.Equivalence.inverseBraided`: the inverse of a monoidal equivalence between
  braided categories is braided.

## Implementation notes

Mathlib has `CategoryTheory.Equivalence.inverseMonoidal`, which makes `e.inverse` monoidal as
soon as `e.functor` is, but no braided analogue: the only braided transport available there is
`CategoryTheory.Monoidal.Transported.instBraidedCategory` and the instances beside it, which are
special-cased to the category `Monoidal.Transported e` carrying the transported monoidal
structure. The argument used here is the one used for `Monoidal.Transported`, generalised to an
arbitrary equivalence `e : C ≌ D`: the composite `e.inverse ⋙ e.functor` is lax braided because
it is monoidally isomorphic to the identity, and the braiding identity for `e.inverse` follows
from that of the composite by cancelling the (invertible) tensorator of `e.functor` and using
that `e.functor` is faithful.

`Equivalence.inverseMonoidal` makes `e.IsMonoidal` hold, but Mathlib only records this as an
`example` guarded by a transparency option, so the instance
`Equivalence.isMonoidal_inverseMonoidal` is provided here; it is what makes `e.unit` and
`e.counit` monoidal natural transformations and hence makes the isomorphism to the identity
functor usable.

Following `Equivalence.inverseMonoidal`, the structures produced are `def`s carrying
`@[instance_reducible]` rather than `instance`s: `e.functor.Braided` and `e.inverse.Braided`
together would otherwise create an instance diamond on the monoidal structures.
-/

@[expose] public section

open CategoryTheory Category MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe v₁ v₂ u₁ u₂

namespace CategoryTheory.Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D]

noncomputable section

attribute [local instance] inverseMonoidal

/-- The adjunction `e.functor ⊣ e.inverse` underlying an equivalence `e : C ≌ D` with
`e.functor` monoidal is compatible with the monoidal structure that
`CategoryTheory.Equivalence.inverseMonoidal` puts on `e.inverse`: that structure is by
construction the one obtained from the adjunction. -/
instance isMonoidal_inverseMonoidal (e : C ≌ D) [e.functor.Monoidal] : e.IsMonoidal :=
  ⟨rfl, fun _ _ ↦ rfl⟩

variable [BraidedCategory C] [BraidedCategory D] (e : C ≌ D) [e.functor.Braided]

/-- For a braided monoidal equivalence `e : C ≌ D`, the composite `e.inverse ⋙ e.functor` is
lax braided: the counit of `e` is a monoidal isomorphism from it to `𝟭 D`, which is lax
braided. -/
@[instance_reducible]
def inverseCompFunctorLaxBraided : (e.inverse ⋙ e.functor).LaxBraided :=
  Functor.LaxBraided.ofNatIso e.symm.unitIso

attribute [local instance] inverseCompFunctorLaxBraided in
/-- The inverse of a monoidal equivalence between braided categories is lax braided: for the
monoidal structure of `CategoryTheory.Equivalence.inverseMonoidal`, the tensorator of
`e.inverse` commutes with the braidings. -/
@[instance_reducible]
def inverseLaxBraided : e.inverse.LaxBraided where
  braided X Y := by
    apply e.functor.map_injective
    rw [← cancel_epi (μ e.functor (e.inverse.obj X) (e.inverse.obj Y)),
      e.functor.map_comp, e.functor.map_comp, ← assoc, ← assoc,
      Functor.LaxBraided.braided (F := e.functor)]
    have h := Functor.LaxBraided.braided (F := e.inverse ⋙ e.functor) X Y
    rw [Functor.LaxMonoidal.comp_μ, Functor.LaxMonoidal.comp_μ] at h
    simpa only [Functor.comp_obj, Functor.comp_map, assoc] using h

attribute [local instance] inverseLaxBraided in
/-- The inverse of a monoidal equivalence between braided categories is braided, for the
monoidal structure of `CategoryTheory.Equivalence.inverseMonoidal`. When `C` and `D` are
symmetric monoidal this says that the inverse of a symmetric monoidal equivalence is symmetric
monoidal. -/
@[instance_reducible]
def inverseBraided : e.inverse.Braided where

end

end CategoryTheory.Equivalence

end
