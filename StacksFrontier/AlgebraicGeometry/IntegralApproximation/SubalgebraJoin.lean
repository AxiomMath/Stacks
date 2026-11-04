module

public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.CategoryTheory.WithTerminal.Cone
public import StacksFrontier.CategoryTheory.Limits.UnderImages
public import StacksFrontier.CategoryTheory.Sites.RingSubsheaf
public import StacksFrontier.AlgebraicGeometry.IntegralApproximation.Subalgebras

/-!
# The join of two subalgebras of an algebra sheaf

Let `X` be a scheme and `A` a sheaf of commutative `𝒪_X`-algebras, that is an object of
`Stacks.RelativeSpec.AlgebraSheaf X = Under X.sheaf`.  This file equips `Subobject A` with a
join: two subalgebras `B₁, B₂ ⊆ A` have a smallest common upper bound `B₁ ⊔ B₂`, with the two
inclusions `B₁ ≤ B₁ ⊔ B₂`, `B₂ ≤ B₁ ⊔ B₂` and the universal property
`B₁ ≤ W → B₂ ≤ W → B₁ ⊔ B₂ ≤ W`.

This is the instance `CategoryTheory.Subobject.semilatticeSup`, which Mathlib provides for any
category with images and binary coproducts, and the content of the file is that
`Under X.sheaf` has both.  Binary coproducts are pushouts of the structure morphisms, which
exist because `X.sheaf` lives in a category of sheaves with all the colimits that
`CommRingCat` has.  Images are the harder half: `Under X.sheaf` is *not* abelian, and Mathlib's
only image factorisation for sheaves is for type-valued ones, so the image of a morphism of
sheaves of commutative rings is built in
`StacksFrontier.CategoryTheory.Sites.RingSubsheaf` and transported to the under category in
`StacksFrontier.CategoryTheory.Limits.UnderImages`.

The join is the Lean counterpart of the upper bound used in the proof of [Stacks, Tag 05JT],
where it is described as the image of `A₁ ⊗_{𝒪_X} A₂ → A`.

## Main results

* `Stacks.RelativeSpec.exists_isLUB_subobject`: two subalgebras of an algebra sheaf have a least
  upper bound among the subalgebras of that sheaf.
* `Stacks.RelativeSpec.isFiltered_finiteTypeSubalgebra_of_sup`: the directedness assertion of
  [Stacks, Tag 05JT] follows once the join of two finite type quasi-coherent subalgebras is
  known to be quasi-coherent and of finite type.
* `Stacks.RelativeSpec.isFiltered_finiteSubalgebra_of_sup`: the same reduction for the
  directedness assertion of [Stacks, Tag 0817] (1), for an integral algebra sheaf.

## Implementation notes

Neither assertion of [Stacks, Tag 05JT] is proved here, and nothing in this file is tagged.
What the join supplies is the *existence* of upper bounds; that the join of two finite type
quasi-coherent subalgebras is again quasi-coherent and of finite type — which is what the Stacks
Project's "some details omitted" covers — is not proved, and is the remaining content of the
directedness half of that tag.

`Stacks.RelativeSpec.hasColimitsOfShape_withInitial_topCatSheaf` is needed because
`TopCat.Sheaf C Y` is a `def` for `CategoryTheory.Sheaf (Opens.grothendieckTopology Y) C` rather
than an abbreviation, so an instance stated for the latter is not found for the former; and it
is fed to `CategoryTheory.Under.hasColimit_of_hasColimit_liftFromUnder` as a term rather than
left to instance search, which otherwise explores `HasColimitsOfShape (Discrete WalkingPair)` on
the sheaf category itself and exhausts its heartbeats.

## References

* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.RelativeSpec

/-- Colimits of shape `WithInitial (Discrete WalkingPair)` in sheaves of commutative rings on a
topological space, in the `TopCat.Sheaf` spelling. -/
theorem hasColimitsOfShape_withInitial_topCatSheaf (Y : TopCat.{u}) :
    HasColimitsOfShape (WithInitial (Discrete WalkingPair)) (TopCat.Sheaf CommRingCat.{u} Y) :=
  inferInstanceAs (HasColimitsOfShape (WithInitial (Discrete WalkingPair))
    (Sheaf (Opens.grothendieckTopology Y) CommRingCat.{u}))

/-- An under category of sheaves of commutative rings on a topological space has binary
coproducts: they are the pushouts of the two structure morphisms. -/
noncomputable instance hasBinaryCoproducts_under_topCatSheaf {Y : TopCat.{u}}
    (A : TopCat.Sheaf CommRingCat.{u} Y) : HasBinaryCoproducts (Under A) where
  has_colimit F :=
    have := hasColimitsOfShape_withInitial_topCatSheaf Y
    Under.hasColimit_of_hasColimit_liftFromUnder F

variable {X : Scheme.{u}} (A : AlgebraSheaf X)

/-- Two subalgebras of a sheaf of commutative `𝒪_X`-algebras have a least upper bound among the
subalgebras of that sheaf: their join `B₁ ⊔ B₂`.

This is `CategoryTheory.Subobject.semilatticeSup` made explicit; see the module documentation
for where the two instances it needs come from. -/
theorem exists_isLUB_subobject (B₁ B₂ : Subobject A) :
    ∃ Z : Subobject A, B₁ ≤ Z ∧ B₂ ≤ Z ∧ ∀ W : Subobject A, B₁ ≤ W → B₂ ≤ W → Z ≤ W :=
  ⟨B₁ ⊔ B₂, le_sup_left, le_sup_right, fun _ ↦ sup_le⟩

/-- **The directedness assertion of [Stacks, Tag 05JT], reduced to the join.** If `A` has at
least one finite type quasi-coherent subalgebra, and the join of any two of them is again
quasi-coherent and of finite type, then the finite type quasi-coherent subalgebras of `A` form a
filtered category.

The hypothesis is what remains of the directedness half of [Stacks, Tag 05JT]: the existence of
upper bounds is supplied by `Stacks.RelativeSpec.exists_isLUB_subobject`, so only the two
finiteness statements about the join are missing. -/
theorem isFiltered_finiteTypeSubalgebra_of_sup
    (h₀ : ∃ B : Subobject A, finiteTypeSubalgebraProperty A B)
    (h : ∀ B₁ B₂ : Subobject A, finiteTypeSubalgebraProperty A B₁ →
      finiteTypeSubalgebraProperty A B₂ → finiteTypeSubalgebraProperty A (B₁ ⊔ B₂)) :
    IsFiltered (FiniteTypeSubalgebra A) :=
  (isFiltered_finiteTypeSubalgebra_iff A).2
    ⟨h₀, fun B₁ B₂ h₁ h₂ ↦ ⟨B₁ ⊔ B₂, h B₁ B₂ h₁ h₂, le_sup_left, le_sup_right⟩⟩

/-- **The directedness assertion of [Stacks, Tag 0817] (1), reduced to the join.** The same
reduction for an integral algebra sheaf, where finite and finite type subalgebras agree. -/
theorem isFiltered_finiteSubalgebra_of_sup {A : AlgebraSheaf X} (hA : A.IsIntegral)
    (h₀ : ∃ B : Subobject A, finiteTypeSubalgebraProperty A B)
    (h : ∀ B₁ B₂ : Subobject A, finiteTypeSubalgebraProperty A B₁ →
      finiteTypeSubalgebraProperty A B₂ → finiteTypeSubalgebraProperty A (B₁ ⊔ B₂)) :
    IsFiltered (FiniteSubalgebra A) :=
  isFiltered_finiteSubalgebra_of_isFiltered hA (isFiltered_finiteTypeSubalgebra_of_sup A h₀ h)

end Stacks.RelativeSpec

end
