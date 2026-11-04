module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringDerivedGlobalSections

/-!
# Derived descent along the augmentation of a hypercovering of an object

Let `C` be a site with fibre products, let `X` be an object of `C` and let `K` be a simplicial
object of `SR(C, X) = FormalCoproduct (Over X)`; a hypercovering of `X` in the sense of
Stacks 01G5 is such a `K` satisfying covering conditions in every degree. Replacing `C` by the
slice site `C/X` everywhere in the simplicial-site apparatus of Stacks 0D8B gives the simplicial
family of sites `n ↦ (C/X)/K_n`, its total site `(C/K)_total`, and the augmentation
`a : Sh((C/K)_total) ⟶ Sh(C/X)`. That substitution is the content of Stacks 0D89 and 0D8C, and
it is what turns Stacks 0D8H and 0D8I into Stacks 09X7 and 0D8M.

This file carries out the substitution for the two derived statements of Section 85.19:

* **Stacks 09X7**, `RΓ(X, E) = RΓ((C/K)_total, a⁻¹E)` for `E` in `D(C/X)`, and
* **Stacks 0D8M**, that `a⁻¹ : D⁺(C/X) ⟶ D⁺_𝒜((C/K)_total)` is an equivalence with quasi-inverse
  `Ra_*`, where `𝒜 ⊂ Ab((C/K)_total)` is the weak Serre subcategory of cartesian abelian sheaves
  of Stacks 0D7J.

The site of the substitution is `(Over X, P.toGrothendieck.over X)` and the augmentation is
`CategoryTheory.SimplicialSemiRepresentable.situationAugmentation` of Stacks 0D8B taken there, so
the general-augmentation theorems of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringDerivedGlobalSections.lean` and of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringBoundedBelowEquivalence.lean` apply
directly. Neither statement is obtained from the absolute Stacks 0D8H or 0D8I: those are the same
general theorems instantiated at the augmentation of a hypercovering of a *site*, over a
different site and a different augmentation, and neither implies the statements below.

## Main definitions

* `CategoryTheory.SimplicialSemiRepresentable.situationOver` and `.augmentationOver`: the
  simplicial-site situation `n ↦ (C/X)/K_n` of Stacks 0D8B over `C/X`, and its augmentation.
* `CategoryTheory.SimplicialSemiRepresentable.derivedGlobalSectionsInverseImageIsoOver`:
  **Stacks 09X7**, the isomorphism `RΓ(X, -) ≅ a⁻¹ ⋙ RΓ((C/K)_total, -)` of functors on the
  unbounded derived category of abelian sheaves on `C/X`.
* `CategoryTheory.SimplicialSemiRepresentable.derivedTotalInverseImageEquivalenceOver`:
  **Stacks 0D8M**, the equivalence `D⁺(C/X) ≌ D⁺_𝒜((C/K)_total)`.

## Main results

* `CategoryTheory.SimplicialSemiRepresentable`
  `.derivedTotalInverseImageEquivalenceOver_functor`: the forward functor of the equivalence of
  Stacks 0D8M is the restriction of `a⁻¹` to the bounded below subcategories, on the nose.

## What the two statements carry

Both carry the two inputs of Stacks 0D8L — which over `C/X` play the role the two inputs of
Stacks 0D8G play over `C` — in the shape in which the general-augmentation theorems consume them:
`hunit`, that the underived unit `F ⟶ a_*a⁻¹F` of the augmentation adjunction on abelian sheaves
is an isomorphism, and `hacyclic`, that `a⁻¹` of a K-injective complex computes `Ra_*`. See the
module docstring of
`StacksFrontier/CategoryTheory/Sites/Simplicial/HypercoveringObjectDerivedPushforward.lean` for why
neither is discharged in this library.

Stacks 09X7 carries in addition `hΓ`, the **underived** identity
`Γ(C/X, a_*F) = Γ((C/K)_total, F)` on which the factorisation of Stacks 08J6 rests; the derived
half of Stacks 08J6 is *not* assumed, being supplied by
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedGlobalSectionsPushforwardIso`.
Stacks 0D8M carries in addition `hsurj`, the remaining clause of Stacks 0D8K (2): every cartesian
abelian sheaf on the total site lies in the essential image of `a⁻¹`. Each clause string names
what it carries.

## Implementation notes

The hypothesis that `C` has fibre products is the `HasPullbacks C` instance; it makes `Over X`
have pullbacks, hence makes the localized topology `P.toGrothendieck.over X` admit pullbacks of
covering families, which is what the simplicial family of sites of Stacks 0D8B requires. The
pretopology `P` is named rather than a topology because the hypercovering predicate of
Stacks 01G5 is stated for covering families; the site `C/X` is the Grothendieck topology it
generates, localized at `X`.

Nothing below constrains `K`, exactly as in Stacks 0D8L: the augmentation, its derived functors
and all the comparisons exist for every simplicial semi-representable object over `X`, and the
covering conditions of Stacks 01G5 enter only through `hunit`, `hacyclic` and `hsurj`. The
statements are therefore more general than the source's, which assumes `K` to be a hypercovering
of `X`, and specialize to it.

`RΓ(X, -)` is `CategoryTheory.SimplicialSiteSituation.Augmentation.derivedGlobalSectionsBase`
taken at the site `C/X`, that is the total right derived functor of `CategoryTheory.Sheaf.Γ` of
that site. No terminal object is used in its construction, but `C/X` does have one, namely `X`
itself, which is why this is derived global sections *over `X`*.

`D⁺(C/X)` is `DerivedCategoryB.derivedCategoryBPlus` of the weak Serre subcategory of *all*
abelian sheaves on `C/X`, which is cohomological boundedness below and nothing more; that is
`CategoryTheory.SimplicialSiteSituation.Augmentation.derivedCategoryBPlus_top_iff`.

## References

* [Stacks Project, Tag 09X7](https://stacks.math.columbia.edu/tag/09X7)
* [Stacks Project, Tag 0D8M](https://stacks.math.columbia.edu/tag/0D8M)
* [Stacks Project, Tag 0D8H](https://stacks.math.columbia.edu/tag/0D8H)
* [Stacks Project, Tag 0D8I](https://stacks.math.columbia.edu/tag/0D8I)
* [Stacks Project, Tag 0D8L](https://stacks.math.columbia.edu/tag/0D8L)
* [Stacks Project, Tag 0D8K](https://stacks.math.columbia.edu/tag/0D8K)
* [Stacks Project, Tag 0D8C](https://stacks.math.columbia.edu/tag/0D8C)
* [Stacks Project, Tag 0D89](https://stacks.math.columbia.edu/tag/0D89)
* [Stacks Project, Tag 0D8B](https://stacks.math.columbia.edu/tag/0D8B)
* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 08J6](https://stacks.math.columbia.edu/tag/08J6)
* [Stacks Project, Tag 01G5](https://stacks.math.columbia.edu/tag/01G5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialSiteSituation Opposite

universe u

namespace CategoryTheory.SimplicialSemiRepresentable

attribute [local instance] HasDerivedCategory.standard

variable {C : Type u} [SmallCategory C] [HasPullbacks C] (P : Pretopology C) {X : C}
  (K : SimplicialObject (FormalCoproduct.{u} (Over X)))

/-! ### The simplicial-site situation over an object -/

/-- The simplicial family of sites `n ↦ (C/X)/K_n` of Stacks 0D8B, read as a simplicial-site
situation: the construction of Stacks 0D8B carried out over the slice site `C/X` instead of `C`,
which is the substitution Stacks 0D89 and Stacks 0D8C licence. -/
abbrev situationOver : SimplicialSiteSituation.{u} :=
  situation (P.toGrothendieck.over X) K

/-- The augmentation `a : Sh((C/K)_total) ⟶ Sh(C/X)` of Stacks 0D8B over the slice site `C/X`:
the one given by the degree-zero localization functor `j_0 : (C/X)/K_0 ⥤ C/X`. -/
abbrev augmentationOver :
    Augmentation (situationOver P K) (Cat.of (Over X)) (P.toGrothendieck.over X) :=
  situationAugmentation (P.toGrothendieck.over X) K

/-! ### Derived global sections over the object -/

/-- **Stacks 09X7**, granted the inputs the library does not have. For a site `C` with fibre
products, an object `X` of `C`, a simplicial semi-representable object `K` over `X` — in
particular a hypercovering of `X` — and the augmentation `a : Sh((C/K)_total) ⟶ Sh(C/X)` of
Stacks 0D8B read over the slice site, derived global sections over `X` are derived global
sections on the total site of the inverse image:

`RΓ(X, E) = RΓ((C/K)_total, a⁻¹E)`.

The statement is an isomorphism of functors on the *unbounded* derived category of abelian
sheaves on `C/X`, so it holds at every object `E` of `D(C/X)` with no boundedness assumption,
which is the form the source states.

Three hypotheses are carried. `hunit` and `hacyclic` are the two inputs of Stacks 0D8L, the
statement over `C/X` of what Stacks 0D8G states over `C`: the first is the degree-zero
identification of Stacks 0D8K, that the underived unit `F ⟶ a_*a⁻¹F` is an isomorphism, and the
second is that `a⁻¹` of a K-injective complex computes `Ra_*`. `hΓ` is the underived identity
`Γ(C/X, a_*F) = Γ((C/K)_total, F)` on which the factorisation of Stacks 08J6 rests. The derived
content of Stacks 08J6 is *not* assumed: see the module docstring. -/
@[stacks 09X7 "RESTRICTED: granted the two inputs of Tag 0D8L — the underived unit F = a_*a⁻¹F
and the Ra_*-acyclicity of a⁻¹ of a K-injective complex — and the underived identity
Γ(C/X, a_*F) = Γ(total, F); stated for every simplicial semi-representable object over X,
hence for a hypercovering of X"]
def derivedGlobalSectionsInverseImageIsoOver
    (hunit : IsIso (Augmentation.abelianTotalAdjunction (situationOver P K) (Cat.of (Over X))
      (P.toGrothendieck.over X) (augmentationOver P K)).unit)
    (hacyclic : Augmentation.InverseImageComputesDerivedPushforward (situationOver P K)
      (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationOver P K))
    (hΓ : Augmentation.abelianTotalPushforward (situationOver P K) (Cat.of (Over X))
          (P.toGrothendieck.over X) (augmentationOver P K) ⋙
        Sheaf.Γ (P.toGrothendieck.over X) AddCommGrpCat.{u} ≅
      Sheaf.Γ (situationOver P K).totalTopology AddCommGrpCat.{u}) :
    Augmentation.derivedGlobalSectionsBase (Cat.of (Over X)) (P.toGrothendieck.over X) ≅
      Augmentation.derivedTotalInverseImage (situationOver P K) (Cat.of (Over X))
          (P.toGrothendieck.over X) (augmentationOver P K) ⋙
        Augmentation.derivedGlobalSectionsTotal (situationOver P K) :=
  Augmentation.derivedGlobalSectionsInverseImageIso _ _ _ _ hunit hacyclic hΓ

/-! ### The bounded below equivalence over the object -/

section Equivalence

variable
  (hunit : IsIso (Augmentation.abelianTotalAdjunction (situationOver P K) (Cat.of (Over X))
    (P.toGrothendieck.over X) (augmentationOver P K)).unit)
  (hacyclic : Augmentation.InverseImageComputesDerivedPushforward (situationOver P K)
    (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationOver P K))
  (hsurj : ∀ G : Sheaf (situationOver P K).totalTopology AddCommGrpCat.{u},
    (situationOver P K).IsCartesianAbSheaf G →
      (Augmentation.totalInverseImageAb (situationOver P K) (Cat.of (Over X))
        (P.toGrothendieck.over X) (augmentationOver P K)).essImage G)

include hunit hacyclic in
/-- The canonical map `E ⟶ Ra_* a⁻¹ E` is invertible at every object of `D(C/X)`, granted the two
inputs of Stacks 0D8L. This is the statement of Stacks 0D8L for the augmentation of Stacks 0D8B
read over the slice site `C/X`, with those inputs in the shape the general-augmentation theorems
consume them. -/
theorem isIso_derivedAugmentationUnitOver_app_of_inputs
    (E : DerivedCategory (Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u})) :
    IsIso ((Augmentation.derivedAugmentationUnit (situationOver P K) (Cat.of (Over X))
      (P.toGrothendieck.over X) (augmentationOver P K)).app E) :=
  have := Augmentation.isIso_derivedAugmentationUnit _ _ _ _ hunit hacyclic
  NatIso.isIso_app_of_isIso _ E

include hsurj in
/-- **Stacks 0D8M**, granted the inputs the library does not have. For a site `C` with fibre
products, an object `X` of `C`, a simplicial semi-representable object `K` over `X` — in
particular a hypercovering of `X` — the augmentation `a` of Stacks 0D8B read over the slice site
`C/X`, and the weak Serre subcategory `𝒜 ⊂ Ab((C/K)_total)` of cartesian abelian sheaves of
Stacks 0D7J, the derived inverse image is an equivalence

`a⁻¹ : D⁺(C/X) ⟶ D⁺_𝒜((C/K)_total)`

with quasi-inverse `Ra_*`. Both functors of the equivalence are the restrictions of `a⁻¹` and of
`Ra_*` on the nose, since the equivalence is the restricted adjunction; for the forward functor
this is `derivedTotalInverseImageEquivalenceOver_functor`.

Three hypotheses are carried. `hunit` and `hacyclic` are the two inputs of Stacks 0D8L, the
statement over `C/X` of what Stacks 0D8G states over `C`. `hsurj` is the remaining clause of
Stacks 0D8K (2), that every cartesian abelian sheaf on the total site lies in the essential image
of `a⁻¹`. The derived content — that both functors restrict to the bounded below subcategories,
that the cohomology sheaves of `a⁻¹E` are cartesian, and the propagation of the counit from `𝒜`
to all of `D⁺_𝒜` — is *not* assumed. -/
@[stacks 0D8M "RESTRICTED: granted the two inputs of Tag 0D8L — the underived unit F = a_*a⁻¹F
and the Ra_*-acyclicity of a⁻¹ of a K-injective complex — and the essential surjectivity clause
of Tag 0D8K (2); stated for every simplicial semi-representable object over X, hence for a
hypercovering of X"]
def derivedTotalInverseImageEquivalenceOver :
    (DerivedCategoryB.derivedCategoryBPlus
        (⊤ : ObjectProperty
          (Sheaf (P.toGrothendieck.over X) AddCommGrpCat.{u}))).FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryBPlus
        ((situationOver P K).IsCartesianAbSheaf)).FullSubcategory :=
  have hall : ∀ E, IsIso ((Augmentation.derivedTotalAdjunction (situationOver P K)
      (Cat.of (Over X)) (P.toGrothendieck.over X) (augmentationOver P K)).unit.app E) :=
    isIso_derivedAugmentationUnitOver_app_of_inputs P K hunit hacyclic
  Augmentation.derivedTotalInverseImageEquivalence _ _ _ _ (fun E _ ↦ hall E)
    (fun E hE ↦ Augmentation.isIso_derivedCounit_app_of_isCartesian _ _ _ _ hall hsurj E hE)

include hunit hacyclic hsurj in
/-- **Stacks 0D8M, the forward functor of the equivalence is `a⁻¹`:** it is the restriction of the
derived inverse image to the bounded below subcategories. -/
@[stacks 0D8M "RESTRICTED: the forward functor of the equivalence is a⁻¹, for the equivalence
built granted the two inputs of Tag 0D8L and the essential surjectivity clause of Tag 0D8K (2)"]
theorem derivedTotalInverseImageEquivalenceOver_functor :
    (derivedTotalInverseImageEquivalenceOver P K hunit hacyclic hsurj).functor =
      Augmentation.derivedTotalInverseImagePlus (situationOver P K) (Cat.of (Over X))
        (P.toGrothendieck.over X) (augmentationOver P K) :=
  rfl

end Equivalence

end CategoryTheory.SimplicialSemiRepresentable

end
