module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringObjectDerivedDescent

/-!
# The two bounded below functors of derived descent for a hypercovering of an object

Let `C` be a site with fibre products, let `X` be an object of `C` and let `K` be a simplicial
object of `SR(C, X) = FormalCoproduct (Over X)`; a hypercovering of `X` in the sense of
Stacks 01G5 is such a `K` satisfying covering conditions in every degree. Substituting the slice
site `C/X` for `C` throughout the simplicial-site apparatus of Stacks 0D8B — the substitution of
Stacks 0D89 and Stacks 0D8C — gives the simplicial family of sites `n ↦ (C/X)/K_n`, its total
site `(C/K)_total`, and the augmentation `a : Sh((C/K)_total) ⟶ Sh(C/X)`.

Stacks 0D8M asserts that `a⁻¹` is an *equivalence*

`D⁺(C/X) ⟶ D⁺_𝒜((C/K)_total)`

with quasi-inverse `Ra_*`, where `𝒜 ⊂ Ab((C/K)_total)` is the weak Serre subcategory of
cartesian abelian sheaves of Stacks 0D7J. Before the equivalence can be asserted, the two
functors it names have to go where the source says they go: `a⁻¹` has to send a bounded below
complex on `C/X` to a bounded below complex on the total site *whose cohomology sheaves are
cartesian*, and `Ra_*` has to send a bounded below complex with cartesian cohomology sheaves
back to a bounded below one. This file proves exactly those two statements over `C/X`, with no
condition beyond the source's own, and assembles the two restricted functors and the restricted
adjunction between them.

The equivalence itself is **not** proved here, and no declaration below asserts it. It rests on
the invertibility of the canonical map `E ⟶ Ra_*a⁻¹E` of Stacks 0D8L, which this library does
not have for the augmentation of a hypercovering; see "What is still missing" below.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.derivedPlusBaseOver` and
  `.derivedPlusCartesianOver`: the two full subcategories `D⁺(C/X)` and
  `D⁺_𝒜((C/K)_total)` of Stacks 0D8M, as object properties of the unbounded derived categories.
* `CategoryTheory.SimplicialSemiRepresentable.derivedTotalInverseImageOverHomologyObjIso`:
  `H^q(a⁻¹E) = a⁻¹H^q(E)`, which is why `a⁻¹` lands in the cartesian subcategory.
* `CategoryTheory.SimplicialSemiRepresentable.derivedTotalInverseImagePlusOver` and
  `.derivedTotalPushforwardPlusOver`: the restrictions `a⁻¹ : D⁺(C/X) ⥤ D⁺_𝒜((C/K)_total)` and
  `Ra_* : D⁺_𝒜((C/K)_total) ⥤ D⁺(C/X)`, the two functors Stacks 0D8M names.
* `CategoryTheory.SimplicialSemiRepresentable.derivedTotalAdjunctionBoundedBelowOver`: the
  adjunction `a⁻¹ ⊣ Ra_*` between those two subcategories, obtained by restricting the derived
  adjunction on the unbounded derived categories.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.isCartesianAbSheaf_homology_derivedTotalInverseImageOver_obj`: every cohomology sheaf of
  `a⁻¹E` is cartesian, which is Stacks 0D7H read over `C/X`.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.derivedCategoryBPlus_derivedTotalInverseImageOver_obj`: **the first half of the
  well-definedness clause of Stacks 0D8M** — `a⁻¹` sends `D⁺(C/X)` into `D⁺_𝒜((C/K)_total)`.
* `CategoryTheory.SimplicialSemiRepresentable`
  `.derivedCategoryBPlus_derivedTotalPushforwardOver_obj`: **the second half** — `Ra_*` sends
  `D⁺_𝒜((C/K)_total)` into `D⁺(C/X)`.

## What is still missing

Everything below is unconditional: the only binders are the source's own — `C` a site with
fibre products, `X` an object of `C`, and `K` a simplicial semi-representable object over `X`.
Nothing constrains `K`, so in particular the statements hold for a hypercovering of `X`, which
is the case Stacks 0D8M treats.

The remaining content of Stacks 0D8M — that the restricted adjunction is an adjoint equivalence
— needs the canonical map `E ⟶ Ra_*a⁻¹E` of Stacks 0D8L to be invertible, and that in turn needs
two inputs this library does not prove for the augmentation of a hypercovering: the underived
identification `F = a_*a⁻¹F`, which is the abelian form of Stacks 0D8E and rests on the abelian
form of Stacks 0D86, available here for sheaves of sets only; and the `Ra_*`-acyclicity of `a⁻¹`
of a K-injective complex, which the source gets from the spectral sequence of Stacks 0D7A. See
the module docstrings of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringCohomologicalDescent.lean` and
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringObjectDerivedPushforward.lean`.

## Implementation notes

The condition that `C` has fibre products is the `HasPullbacks C` instance; it makes `Over X`
have pullbacks, hence makes the localized topology `P.toGrothendieck.over X` admit pullbacks of
covering families, which is what the simplicial family of sites of Stacks 0D8B requires. The
pretopology `P` is named rather than a topology because the hypercovering predicate of
Stacks 01G5 is stated for covering families; the site `C/X` is the Grothendieck topology it
generates, localized at `X`.

`D⁺(C/X)` is the bounded below subcategory attached to the weak Serre subcategory of *all*
abelian sheaves on `C/X`, which is how the source reads it; the condition on the cohomology
sheaves is then vacuous, as
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedCategoryBPlus_top_iff` records.
Taking the subcategory downstairs to be everything is what makes the second half of the
well-definedness clause a statement about boundedness alone.

The two restrictions are formed with `ObjectProperty.lift`, so each is the ambient derived
functor on the nose, and the adjunction between them is the restriction of the derived
adjunction rather than one assembled by hand. That is what will make `Ra_*` the quasi-inverse,
on the nose, once the equivalence becomes available.

## References

* [Stacks Project, Tag 0D8M](https://stacks.math.columbia.edu/tag/0D8M)
* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0D8I](https://stacks.math.columbia.edu/tag/0D8I)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D8C](https://stacks.math.columbia.edu/tag/0D8C)
* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialSiteSituation Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-! ### The two subcategories of Stacks 0D8M -/

/-- `D⁺(C/X)`: the bounded below objects of the derived category of abelian sheaves on the slice
site `C/X`. The source writes this `D⁺_{Ab(C/X)}(C/X)`, the bounded below subcategory attached
to the weak Serre subcategory of all abelian sheaves; the condition on the cohomology sheaves is
vacuous. -/
abbrev derivedPlusBaseOver (Y : C) :
    ObjectProperty
      (DerivedCategory (Sheaf (P.toGrothendieck.over Y) AddCommGrpCat.{u})) :=
  Augmentation.derivedPlusBase (Cat.of (Over Y)) (P.toGrothendieck.over Y)

/-- `D⁺_𝒜((C/K)_total)`: the bounded below objects of the derived category of abelian sheaves on
the total site all of whose cohomology sheaves are cartesian, `𝒜` being the weak Serre
subcategory of Stacks 0D7J. -/
abbrev derivedPlusCartesianOver :
    ObjectProperty
      (DerivedCategory (Sheaf (situationOver P K).totalTopology AddCommGrpCat.{u})) :=
  Augmentation.derivedPlusCartesian (situationOver P K)

/-! ### The cohomology sheaves of an inverse image are cartesian -/

/-- **`H^q(a⁻¹E) = a⁻¹H^q(E)`** for the augmentation of the total site of a simplicial
semi-representable object over `X`: the derived inverse image is computed degreewise, `a⁻¹` being
exact, and an exact functor commutes with the cohomology functors. -/
def derivedTotalInverseImageOverHomologyObjIso
    (E : DerivedCategory (Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u})) (q : ℤ) :
    (DerivedCategory.homologyFunctor
          (Sheaf (situationOver P K).totalTopology AddCommGrpCat.{u}) q).obj
        ((Augmentation.derivedTotalInverseImage (situationOver P K) (Cat.of (Over X))
          (P.toGrothendieck.over X) (augmentationOver P K)).obj E) ≅
      (Augmentation.totalInverseImageAb (situationOver P K) (Cat.of (Over X))
          (P.toGrothendieck.over X) (augmentationOver P K)).obj
        ((DerivedCategory.homologyFunctor
          (Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u}) q).obj E) :=
  Augmentation.derivedTotalInverseImageHomologyObjIso (situationOver P K) (Cat.of (Over X))
    (P.toGrothendieck.over X) (augmentationOver P K) E q

/-- **Stacks 0D7H over the slice site `C/X`.** Every cohomology sheaf of `a⁻¹E` is cartesian: it
is `a⁻¹` of a cohomology sheaf of `E` by `derivedTotalInverseImageOverHomologyObjIso`, and every
inverse image along the augmentation is cartesian. -/
theorem isCartesianAbSheaf_homology_derivedTotalInverseImageOver_obj
    (E : DerivedCategory (Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u})) (q : ℤ) :
    (situationOver P K).IsCartesianAbSheaf
      ((DerivedCategory.homologyFunctor
          (Sheaf (situationOver P K).totalTopology AddCommGrpCat.{u}) q).obj
        ((Augmentation.derivedTotalInverseImage (situationOver P K) (Cat.of (Over X))
          (P.toGrothendieck.over X) (augmentationOver P K)).obj E)) :=
  ObjectProperty.prop_of_iso (P := (situationOver P K).IsCartesianAbSheaf)
    (derivedTotalInverseImageOverHomologyObjIso P K E q).symm
    (Augmentation.isCartesianAbSheaf_totalInverseImageAb (situationOver P K) (Cat.of (Over X))
    (P.toGrothendieck.over X) (augmentationOver P K) _)

/-! ### The well-definedness clause of Stacks 0D8M -/

/-- **Stacks Project, Tag 0D8M, the first half of the well-definedness clause.** For a site `C`
with fibre products, an object `X` of `C`, a simplicial semi-representable object `K` over `X` —
in particular a hypercovering of `X` — and the augmentation `a : Sh((C/K)_total) ⟶ Sh(C/X)` of
Stacks 0D8B read over the slice site, the derived inverse image sends `D⁺(C/X)` into
`D⁺_𝒜((C/K)_total)`: it preserves boundedness below, and its cohomology sheaves are cartesian by
`isCartesianAbSheaf_homology_derivedTotalInverseImageOver_obj`.

This is the clause of Stacks 0D8M which says that the functor whose invertibility the source
asserts is defined at all. The invertibility is not proved here. -/
@[stacks 0D8M "the first half of the well-definedness clause only: a⁻¹ sends D⁺(C/X) into
D⁺_𝒜((C/K)_total); the equivalence itself is not proved"]
theorem derivedCategoryBPlus_derivedTotalInverseImageOver_obj
    (E : DerivedCategory (Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u}))
    (hE : DerivedCategoryB.IsBoundedBelow E) :
    derivedPlusCartesianOver P K
      ((Augmentation.derivedTotalInverseImage (situationOver P K) (Cat.of (Over X))
        (P.toGrothendieck.over X) (augmentationOver P K)).obj E) :=
  Augmentation.derivedCategoryBPlus_derivedTotalInverseImage_obj (situationOver P K)
    (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationOver P K) E hE

/-- **Stacks Project, Tag 0D8M, the second half of the well-definedness clause.** In the same
situation the derived direct image sends `D⁺_𝒜((C/K)_total)` into `D⁺(C/X)`. Only boundedness
below is at stake, the weak Serre subcategory on `C/X` being all of `Ab(C/X)`.

This is the clause of Stacks 0D8M which says that the quasi-inverse the source names is defined
at all. That it *is* a quasi-inverse is not proved here. -/
@[stacks 0D8M "the second half of the well-definedness clause only: Ra_* sends
D⁺_𝒜((C/K)_total) into D⁺(C/X); the equivalence itself is not proved"]
theorem derivedCategoryBPlus_derivedTotalPushforwardOver_obj
    (E : DerivedCategory (Sheaf (situationOver P K).totalTopology AddCommGrpCat.{u}))
    (hE : DerivedCategoryB.IsBoundedBelow E) :
    derivedPlusBaseOver P X
      ((Augmentation.derivedTotalPushforward (situationOver P K) (Cat.of (Over X))
        (P.toGrothendieck.over X) (augmentationOver P K)).obj E) :=
  Augmentation.derivedCategoryBPlus_derivedTotalPushforward_obj (situationOver P K)
    (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationOver P K) E hE

/-! ### The two restricted functors and the adjunction between them -/

/-- **`a⁻¹ : D⁺(C/X) ⥤ D⁺_𝒜((C/K)_total)`**, the forward functor Stacks 0D8M names. It is the
derived inverse image on the nose, the restriction being formed with `ObjectProperty.lift`. -/
abbrev derivedTotalInverseImagePlusOver :
    (derivedPlusBaseOver P X).FullSubcategory ⥤ (derivedPlusCartesianOver P K).FullSubcategory :=
  Augmentation.derivedTotalInverseImagePlus (situationOver P K) (Cat.of (Over X))
    (P.toGrothendieck.over X) (augmentationOver P K)

/-- **`Ra_* : D⁺_𝒜((C/K)_total) ⥤ D⁺(C/X)`**, the functor Stacks 0D8M names as the quasi-inverse.
It is the derived direct image on the nose. -/
abbrev derivedTotalPushforwardPlusOver :
    (derivedPlusCartesianOver P K).FullSubcategory ⥤ (derivedPlusBaseOver P X).FullSubcategory :=
  Augmentation.derivedTotalPushforwardPlus (situationOver P K) (Cat.of (Over X))
    (P.toGrothendieck.over X) (augmentationOver P K)

/-- The adjunction `a⁻¹ ⊣ Ra_*` between `D⁺(C/X)` and `D⁺_𝒜((C/K)_total)`, obtained by
restricting the derived adjunction on the unbounded derived categories. Stacks 0D8M asserts that
this adjunction is an adjoint equivalence; that assertion is not proved here. -/
def derivedTotalAdjunctionBoundedBelowOver :
    derivedTotalInverseImagePlusOver P K ⊣ derivedTotalPushforwardPlusOver P K :=
  Augmentation.derivedTotalAdjunctionBoundedBelow (situationOver P K) (Cat.of (Over X))
    (P.toGrothendieck.over X) (augmentationOver P K)

end CategoryTheory.SimplicialSemiRepresentable

end
