module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.ShrinkCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.StrongSerreAbelian

/-!
# Constructible sheaves on a Noetherian scheme form Serre subcategories

Let `X` be a Noetherian scheme and `Λ` a Noetherian ring. On the small étale site of `X`:

1. any subsheaf or quotient sheaf of a constructible sheaf of sets is constructible;
2. the constructible abelian sheaves form a (strong) Serre subcategory of all abelian sheaves;
3. the constructible sheaves of `Λ`-modules form a (strong) Serre subcategory of all sheaves of
   `Λ`-modules.

This is Stacks 09BH, stated here with every input discharged and no instance assumed.

## Main results

* `AlgebraicGeometry.isConstructibleSetSheaf_of_mono_of_epi_and_isSerreClass_abelian_and_module`
  — **Stacks 09BH**, all three parts.

## Implementation notes

A Serre subcategory in the sense of Stacks 02MO is, by Stacks 02MP, a full subcategory containing
zero and closed under subobjects, quotients and extensions; that is exactly
`CategoryTheory.ObjectProperty.IsSerreClass`. The "in particular" clauses of parts (2) and (3),
closure under subobjects and quotients, are two of its fields.

The three parts are assembled from the statements proving them, with their inputs supplied:

* part (1) is `AlgebraicGeometry.isConstructibleSetSheaf_of_mono` and
  `AlgebraicGeometry.isConstructibleSetSheaf_of_epi`, whose two inputs are Stacks 03S8,
  `AlgebraicGeometry.representableIsConstructibleSetSheaf`, and the surjection half of
  Stacks 09Y9, `AlgebraicGeometry.hasFiniteRepresentableCover`;
* part (2) is `AlgebraicGeometry.isSerreClass_isConstructibleAbelianSheaf`, which in addition
  takes Stacks 00YT for the forgetful functor, `AlgebraicGeometry.smallEtaleUnderlyingSetCommutes`;
* part (3) is `AlgebraicGeometry.isSerreClass_isConstructibleModuleSheaf_of_small`.

The inverse images along small étale base change and the sheafifications over slices, which the
definitions of constructibility mention, exist for all three coefficient categories and are found
by instance search, so the statement assumes none of them.

Sheaves of sets take values in `Type (u + 1)` and abelian sheaves in `AddCommGrpCat.{u + 1}`,
the universe of the objects of the small étale site of Stacks 021B. The coefficient ring `Λ` may
live in any universe in which it is small in `Type (u + 1)` — every ring in `Type 0` or in
`Type (u + 1)` qualifies — and its module sheaves take values in `ModuleCat.{u + 1} Λ`.

## References

* [Stacks Project, Tag 09BH](https://stacks.math.columbia.edu/tag/09BH)
* [Stacks Project, Tag 02MP](https://stacks.math.columbia.edu/tag/02MP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u r

namespace AlgebraicGeometry

attribute [local instance high] Stacks.ConstantSheaf.hasSheafify_moduleCat_of_univLE

/-- **Stacks 09BH.** Let `X` be a Noetherian scheme and let `Λ` be a Noetherian ring.

1. Any sub or quotient sheaf of a constructible sheaf of sets on the small étale site of `X` is
   constructible.
2. The constructible abelian sheaves on that site form a (strong) Serre subcategory of all
   abelian sheaves on it; in particular every subsheaf and quotient sheaf of a constructible
   abelian sheaf is constructible.
3. The constructible sheaves of `Λ`-modules on that site form a (strong) Serre subcategory of all
   sheaves of `Λ`-modules on it; in particular every submodule and quotient module of a
   constructible sheaf of `Λ`-modules is constructible.

`CategoryTheory.ObjectProperty.IsSerreClass` is containing zero and closure under subobjects,
quotients and extensions, which is a Serre subcategory by Stacks 02MP. -/
@[stacks 09BH]
public theorem isConstructibleSetSheaf_of_mono_of_epi_and_isSerreClass_abelian_and_module
    (B : BigEtaleSite.{u}) (X : B.Scheme) [IsNoetherian X.obj]
    (Λ : Type r) [CommRing Λ] [IsNoetherianRing Λ] [Small.{u + 1} Λ] :
    ((∀ (F G : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) (i : G ⟶ F),
        Mono i → IsConstructibleSetSheaf B X F → IsConstructibleSetSheaf B X G) ∧
      (∀ (F Q : Sheaf (SmallEtale.topology B X.obj X.property) (Type (u + 1))) (p : F ⟶ Q),
        Epi p → IsConstructibleSetSheaf B X F → IsConstructibleSetSheaf B X Q)) ∧
      ObjectProperty.IsSerreClass
        (fun F : Sheaf (SmallEtale.topology B X.obj X.property) AddCommGrpCat.{u + 1} =>
          IsConstructibleAbelianSheaf B X F) ∧
      ObjectProperty.IsSerreClass
        (fun F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{u + 1} Λ) =>
          IsConstructibleModuleSheaf B X Λ F) :=
  ⟨⟨fun _ _ i hi hF => by
      have := hi
      exact isConstructibleSetSheaf_of_mono B X (representableIsConstructibleSetSheaf B X)
        (hasFiniteRepresentableCover B X) i hF,
    fun _ _ p hp hF => by
      have := hp
      exact isConstructibleSetSheaf_of_epi B X (representableIsConstructibleSetSheaf B X)
        (hasFiniteRepresentableCover B X) p hF⟩,
    isSerreClass_isConstructibleAbelianSheaf B X (smallEtaleUnderlyingSetCommutes B X)
      (representableIsConstructibleSetSheaf B X) (hasFiniteRepresentableCover B X),
    isSerreClass_isConstructibleModuleSheaf_of_small B Λ X⟩

end AlgebraicGeometry

end
