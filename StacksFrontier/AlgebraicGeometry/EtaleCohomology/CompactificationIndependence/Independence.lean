module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Derived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Unbounded
public import StacksFrontier.CategoryTheory.Filtered.CofilteredIsoSystem
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.CompactificationsCofiltered
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Independence of `Rf_!` from the compactification (Stacks 0F7I)

Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact and quasi-separated
schemes and `Λ` a ring. For a compactification `j : X ⟶ X̄` of `X` over `Y` the functor
`Rf_! = R(j̄)_* ∘ j_!` of [Stacks, Tag 0F7H] is `Stacks.EtaleCohomology.derivedLowerShriek`.
[Stacks, Tag 0F7I] says that these functors are, up to canonical isomorphism, independent of
the compactification.

The proof is the source's. Compactifications exist (Tag 0F41) and form a cofiltered category
(Tag 0ATU). A morphism `g : j ⟶ k` of compactifications induces the isomorphism
`Stacks.EtaleCohomology.derivedLowerShriekHomIso`, built from the map of Tag 0F7G, and these
isomorphisms compose (`Stacks.EtaleCohomology.derivedLowerShriekHomIso_comp`). Hence any two
compactifications are compared through a third mapping to both, and by the footnote of the
source the comparison does not depend on the third
(`CategoryTheory.IsCofiltered.isoSystemComparison`).

## Main definitions

* `Stacks.EtaleCohomology.derivedLowerShriekCompactificationIso`: the canonical isomorphism
  between the derived lower shriek functors on `D⁺_tors(X_étale, Λ)` of two compactifications.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompactificationIso`: the same on
  `D(X_étale, Λ)` for a torsion ring `Λ`.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriekUnbounded_independent_of_compactification`:
  **[Stacks, Tag 0F7I]** for `Rf_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)`, `Λ` a torsion ring.
* `Stacks.EtaleCohomology.derivedLowerShriek_independent_of_compactification`:
  **[Stacks, Tag 0F7I]** for `Rf_! : D⁺_tors(X_étale, Λ) ⥤ D⁺_tors(Y_étale, Λ)`.

The two registered statements cover the two functors of the source: the source proves the
first and says the second "is proved in exactly the same way".

## Implementation notes

The coefficient ring is `Λ : Type` and the sheaves are those of
`Stacks.EtaleCohomology.EtaleModules.{u, 0}`, the setting of the functors `Rf_!` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology`; the proper base
change theorem enters through abelian sheaves in that universe. The ring is arbitrary, not
necessarily commutative. A torsion ring is one in which `m • 1 = 0` for some `m > 0`.

## References

* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
* [Stacks Project, Tag 0F7G](https://stacks.math.columbia.edu/tag/0F7G)
* [Stacks Project, Tag 0F41](https://stacks.math.columbia.edu/tag/0F41)
* [Stacks Project, Tag 0ATU](https://stacks.math.columbia.edu/tag/0ATU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- The category of compactifications of a finite type separated morphism to a quasi-compact
quasi-separated scheme: a compactification exists by Nagata's theorem, [Stacks, Tag 0F41]. -/
def categoryOfCompactificationsOf {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    CategoryOfCompactifications.{u} where
  S := Y
  X := Over.mk f
  isQuasiCompact := inferInstance
  isQuasiSeparated := inferInstance
  exists_quasiCompact_compactification := hasCompactification_of_compactSpace_quasiSeparatedSpace f

/-- **The compactifications of `X` over `Y` form a cofiltered category** ([Stacks, Tag 0ATU]). -/
instance isCofiltered_compactificationOf {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f] :
    IsCofiltered (CompactificationOf (Over.mk f)) :=
  CategoryOfCompactifications.isCofiltered (categoryOfCompactificationsOf f)

attribute [local instance] HasDerivedCategory.standard

/-- **The canonical isomorphism between `Rf_!` computed through two compactifications**, on
`D⁺_tors(X_étale, Λ)`: through any compactification `l` mapping to both, it is
`Rf_!^{j₁} ≅ Rf_!^l ≅ Rf_!^{j₂}`, the isomorphisms being those of the two morphisms of
compactifications (`Stacks.EtaleCohomology.derivedLowerShriekHomIso`). -/
def derivedLowerShriekCompactificationIso {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j₁ j₂ : CompactificationOf (Over.mk f)) (Λ : Type) [Ring Λ] :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f j₁ Λ ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f j₂ Λ :=
  IsCofiltered.isoSystemComparison
    (Φ := fun j => (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f j Λ)
    (fun g => derivedLowerShriekHomIso Λ g) j₁ j₂

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f] (Λ : Type) [Ring Λ]

/-- The comparisons of `Stacks.EtaleCohomology.derivedLowerShriekCompactificationIso` compose. -/
theorem derivedLowerShriekCompactificationIso_trans (j k l : CompactificationOf (Over.mk f)) :
    derivedLowerShriekCompactificationIso f j k Λ ≪≫ derivedLowerShriekCompactificationIso f k l Λ =
      derivedLowerShriekCompactificationIso f j l Λ :=
  IsCofiltered.isoSystemComparison_trans _ (fun g h => derivedLowerShriekHomIso_comp Λ g h) j k l

/-- Along a morphism `g : j ⟶ k` of compactifications the comparison
`Rf_!^k ≅ Rf_!^j` is the isomorphism `Stacks.EtaleCohomology.derivedLowerShriekHomIso` of `g`,
built from the map of [Stacks, Tag 0F7G]. -/
theorem derivedLowerShriekCompactificationIso_of_hom {j k : CompactificationOf (Over.mk f)}
    (g : j ⟶ k) :
    derivedLowerShriekCompactificationIso f k j Λ = derivedLowerShriekHomIso Λ g :=
  IsCofiltered.isoSystemComparison_of_hom _ (fun g h => derivedLowerShriekHomIso_comp Λ g h) g

/-- **Stacks Project, Tag 0F7I**, for `Rf_! : D⁺_tors(X_étale, Λ) ⥤ D⁺_tors(Y_étale, Λ)` and an
arbitrary ring `Λ`. Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact and
quasi-separated schemes. Then `X` has a compactification over `Y`, and the functors `Rf_!`
built from the compactifications are, up to canonical isomorphism, independent of the
compactification: the isomorphisms `derivedLowerShriekCompactificationIso f j k Λ` between them
compose, and along every morphism `g : j ⟶ k` of compactifications they are the isomorphism
built from the map of [Stacks, Tag 0F7G] and the composition of derived direct images. -/
@[stacks 0F7I "bounded-below complexes with torsion cohomology sheaves, arbitrary ring Λ",
  sga "4½ Arcata 4.5.3" "more general",
  sga "7 XIII 2.1.6" "more general"]
theorem derivedLowerShriek_independent_of_compactification :
    (∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion) ∧
      (∀ j k l : CompactificationOf (Over.mk f),
        derivedLowerShriekCompactificationIso f j k Λ ≪≫
            derivedLowerShriekCompactificationIso f k l Λ =
          derivedLowerShriekCompactificationIso f j l Λ) ∧
      ∀ {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k),
        derivedLowerShriekCompactificationIso f k j Λ = derivedLowerShriekHomIso Λ g :=
  ⟨hasCompactification_of_compactSpace_quasiSeparatedSpace f,
    derivedLowerShriekCompactificationIso_trans f Λ,
    fun g => derivedLowerShriekCompactificationIso_of_hom f Λ g⟩

/-! ### The unbounded derived category, for a torsion ring -/

/-- **The canonical isomorphism between `Rf_!` computed through two compactifications**, on
`D(X_étale, Λ)` for a torsion ring `Λ`. -/
def derivedLowerShriekUnboundedCompactificationIso {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (j₁ j₂ : CompactificationOf (Over.mk f)) (Λ : Type) [Ring Λ]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    derivedLowerShriekUnbounded.{u, 0} f j₁ Λ ≅ derivedLowerShriekUnbounded.{u, 0} f j₂ Λ :=
  IsCofiltered.isoSystemComparison
    (Φ := fun j => derivedLowerShriekUnbounded.{u, 0} f j Λ)
    (fun g => derivedLowerShriekUnboundedHomIso Λ g hΛ) j₁ j₂

variable (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-- The comparisons of `derivedLowerShriekUnboundedCompactificationIso` compose. -/
@[sga "4 XVII 3.3.2.1" "special case"]
theorem derivedLowerShriekUnboundedCompactificationIso_trans
    (j k l : CompactificationOf (Over.mk f)) :
    derivedLowerShriekUnboundedCompactificationIso f j k Λ hΛ ≪≫
        derivedLowerShriekUnboundedCompactificationIso f k l Λ hΛ =
      derivedLowerShriekUnboundedCompactificationIso f j l Λ hΛ :=
  IsCofiltered.isoSystemComparison_trans _
    (fun g h => derivedLowerShriekUnboundedHomIso_comp Λ g h hΛ) j k l

/-- Along a morphism `g : j ⟶ k` of compactifications the comparison is the isomorphism
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedHomIso` of `g`. -/
theorem derivedLowerShriekUnboundedCompactificationIso_of_hom
    {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k) :
    derivedLowerShriekUnboundedCompactificationIso f k j Λ hΛ =
      derivedLowerShriekUnboundedHomIso Λ g hΛ :=
  IsCofiltered.isoSystemComparison_of_hom _
    (fun g h => derivedLowerShriekUnboundedHomIso_comp Λ g h hΛ) g

/-- **Stacks Project, Tag 0F7I**, for `Rf_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` and a torsion ring
`Λ`. Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact and quasi-separated
schemes. Then `X` has a compactification over `Y`, and the functors `Rf_!` built from the
compactifications are, up to canonical isomorphism, independent of the compactification: the
isomorphisms `derivedLowerShriekUnboundedCompactificationIso f j k Λ hΛ` between them compose,
and along every morphism `g : j ⟶ k` of compactifications they are the isomorphism built from
the map of [Stacks, Tag 0F7G] and the composition of derived direct images. -/
@[stacks 0F7I "unbounded derived category D(X_étale, Λ), Λ a torsion ring",
  sga "4 XVII 5.2.2" "special case",
  sga "4½ Arcata 4.5.3" "more general",
  sga "7 XIII 2.1.6" "more general"]
theorem derivedLowerShriekUnbounded_independent_of_compactification :
    (∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion) ∧
      (∀ j k l : CompactificationOf (Over.mk f),
        derivedLowerShriekUnboundedCompactificationIso f j k Λ hΛ ≪≫
            derivedLowerShriekUnboundedCompactificationIso f k l Λ hΛ =
          derivedLowerShriekUnboundedCompactificationIso f j l Λ hΛ) ∧
      ∀ {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k),
        derivedLowerShriekUnboundedCompactificationIso f k j Λ hΛ =
          derivedLowerShriekUnboundedHomIso Λ g hΛ :=
  ⟨hasCompactification_of_compactSpace_quasiSeparatedSpace f,
    derivedLowerShriekUnboundedCompactificationIso_trans f Λ hΛ,
    fun g => derivedLowerShriekUnboundedCompactificationIso_of_hom f Λ hΛ g⟩

end Stacks.EtaleCohomology
