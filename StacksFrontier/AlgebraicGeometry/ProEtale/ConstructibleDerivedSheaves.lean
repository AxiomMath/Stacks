module

public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstantCoefficientModules
public import StacksFrontier.AlgebraicGeometry.ProEtale.ConstructibleSheaves
public import StacksFrontier.CategoryTheory.Sites.DerivedTensorModuleSheaf.FiniteTorDimension
public import StacksFrontier.Homology.DerivedCategory.KInjectiveProducts
public import StacksFrontier.RingTheory.Dualizing.MapDerivedCategory
import StacksCore.Tactic.StacksAttribute

/-!
# The constructible derived category `D_cons(X, Λ)` of the pro-étale site

Let `Λ` be a Noetherian ring, `I ⊆ Λ` an ideal and `X` a scheme. An object `K` of
`D(X_proét, Λ)` is *constructible* when

* `K` is derived complete with respect to `I`, and
* `K ⊗_Λ^L \underline{Λ/I}` has constructible cohomology sheaves and locally has finite Tor
  dimension.

The constructible objects form the full subcategory `D_cons(X, Λ)` of `D(X_proét, Λ)`.

Here `D(X_proét, Λ)` is the derived category of sheaves of modules over the constant
coefficient ring sheaf `\underline{Λ}` on `X_proét`, the category in which derived completeness
is formulated (Stacks 0999). A sheaf of modules over `\underline{Λ}` is the same thing as a sheaf
of `Λ`-modules (`AlgebraicGeometry.ProEtale.constantCoefficientModuleEquiv`), so this derived
category is equivalent to the derived category of sheaves of `Λ`-modules on `X_proét`, in which
the derived tensor product `- ⊗_Λ^L -` is constructed (Stacks 09BQ). The reduction
`K ⊗_Λ^L \underline{Λ/I}` is the derived extension of scalars along `Λ → Λ/I`, an object of
`D(X_proét, Λ/I)` (Stacks 09BR), and its constructibility and Tor dimension are read there.

## Main definitions

* `AlgebraicGeometry.ProEtale.derivedModuleEquiv`: the equivalence between the derived category
  of sheaves of `Λ`-modules on `X_proét` and `D(X_proét, Λ)`.
* `AlgebraicGeometry.ProEtale.derivedReduction`: the derived reduction
  `K ↦ K ⊗_Λ^L \underline{Λ/I}` from `D(X_proét, Λ)` to sheaves of `Λ/I`-modules.
* `AlgebraicGeometry.ProEtale.HasConstructibleModuleSheafCohomology`: every cohomology sheaf is
  constructible (Stacks 09AJ).
* `AlgebraicGeometry.ProEtale.IsConstructibleViaDerivedReduction`: the constructibility condition
  of Stacks 09C1.
* `AlgebraicGeometry.ProEtale.constructibleDerivedSheavesViaDerivedReduction`: the full subcategory
  `D_cons(X, Λ)`.

## Main results

* `AlgebraicGeometry.ProEtale.hasProductsOfShape_derivedCategory_sheafModuleCat`: countable
  products in the derived category of sheaves of `Λ`-modules on `X_proét`.

## Implementation notes

The coefficient ring lies in the universe `max (u + 1) w` of the module sections, which contains
the universe `u + 1` of the objects of `X_proét`; every ring is isomorphic to one in such a
universe. This is the universe convention under which the derived tensor product and the
derived extension of scalars of Stacks 09BQ and 09BR are constructed.

## References

* [Stacks Project, Tag 09C1](https://stacks.math.columbia.edu/tag/09C1)
* [Stacks Project, Tag 0999](https://stacks.math.columbia.edu/tag/0999)
* [Stacks Project, Tag 08FZ](https://stacks.math.columbia.edu/tag/08FZ)
* [Stacks Project, Tag 09AJ](https://stacks.math.columbia.edu/tag/09AJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u r w

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{u})

section Equivalence

variable (Λ : Type r) [CommRing Λ]

/-- The derived category of sheaves of `Λ`-modules on `X_proét` is equivalent to
`D(X_proét, Λ)`, the derived category of sheaves of modules over the constant coefficient ring
sheaf: this is the equivalence of abelian categories
`AlgebraicGeometry.ProEtale.constantCoefficientModuleEquiv`, applied to complexes. -/
def derivedModuleEquiv :
    DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ)) ≌
      DerivedSheaves.{u, r, w} X Λ :=
  letI e := constantCoefficientModuleEquiv.{u, r, w} X Λ
  letI : e.functor.Additive := Functor.additive_of_preserves_binary_products _
  letI : e.inverse.Additive := Functor.additive_of_preserves_binary_products _
  Dualizing.mapDerivedCategoryEquivalenceOfEquivalence e

/-- The derived category of sheaves of `Λ`-modules on `X_proét` has countable products: it is
equivalent to `D(X_proét, Λ)`, whose countable products come from K-injective resolutions. -/
instance hasProductsOfShape_derivedCategory_sheafModuleCat :
    HasProductsOfShape ℕ
      (DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) r w} Λ))) :=
  have : HasProductsOfShape ℕ (DerivedSheaves.{u, r, w} X Λ) :=
    Stacks.KInjectiveProducts.hasProductsOfShape_derivedCategory_sheafOfModules _
  Adjunction.hasLimitsOfShape_of_equivalence (derivedModuleEquiv.{u, r, w} X Λ).functor

end Equivalence

variable (Λ : Type (max (u + 1) w)) [CommRing Λ] (I : Ideal Λ)

/-- The derived reduction `K ↦ K ⊗_Λ^L \underline{Λ/I}` of an object of `D(X_proét, Λ)`, as an
object of the derived category of sheaves of `Λ/I`-modules on `X_proét`: the derived extension
of scalars along `Λ → Λ/I` of Stacks 09BR. -/
def derivedReduction :
    DerivedSheaves.{u, max (u + 1) w, w} X Λ ⥤
      DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} (Λ ⧸ I))) :=
  (derivedModuleEquiv.{u, max (u + 1) w, w} X Λ).inverse ⋙
    Stacks.ModuleSheaf.derivedExtendScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk I)

section Constructibility

variable [IsNoetherianRing Λ]

/-- Every cohomology sheaf of an object of the derived category of sheaves of `Λ`-modules on
`X_proét` is constructible in the sense of Stacks 09AJ. -/
abbrev HasConstructibleModuleSheafCohomology
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{max (u + 1) w} Λ))) :
    Prop :=
  ∀ i : ℤ, IsConstructibleModuleSheaf'.{u, max (u + 1) w, w} X Λ
    ((DerivedCategory.homologyFunctor _ i).obj L)

/-- **Stacks 09C1.** An object `K` of `D(X_proét, Λ)` is *constructible* with respect to the
ideal `I` of the Noetherian coefficient ring `Λ` when it is derived complete along the ideal
sheaf cut out by `I`, and its derived reduction `K ⊗_Λ^L \underline{Λ/I}` has constructible
cohomology sheaves and locally has finite Tor dimension. -/
@[stacks 09C1 "constructible objects"]
abbrev IsConstructibleViaDerivedReduction (K : DerivedSheaves.{u, max (u + 1) w, w} X Λ) : Prop :=
  RingedSite.IsDerivedComplete.{u + 1, u, max (u + 1) w, w}
      (constantCoefficientRingedSite.{u, max (u + 1) w, w} X Λ)
      (constantCoefficientIdealSheaf.{u, max (u + 1) w, w} X Λ I) K ∧
    (HasConstructibleModuleSheafCohomology.{u, w} X (Λ ⧸ I)
        ((derivedReduction.{u, w} X Λ I).obj K) ∧
      Stacks.ModuleSheaf.LocallyHasFiniteTorDimension ((derivedReduction.{u, w} X Λ I).obj K))

/-- **Stacks 09C1.** The full subcategory `D_cons(X, Λ)` of `D(X_proét, Λ)` on the
constructible objects. -/
@[stacks 09C1 "the full subcategory"]
abbrev constructibleDerivedSheavesViaDerivedReduction :=
  ObjectProperty.FullSubcategory (IsConstructibleViaDerivedReduction.{u, w} X Λ I)

end Constructibility

end AlgebraicGeometry.ProEtale

end
