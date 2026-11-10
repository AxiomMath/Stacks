module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.DerivedCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.UnboundedCoefficientUniverse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence
public import StacksFrontier.CategoryTheory.Filtered.CofilteredIsoSystem
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.CompactificationsCofiltered
public import StacksFrontier.AlgebraicGeometry.NagataCompactification.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Independence of `Rf_!` from the compactification, for coefficients in any universe

Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact and quasi-separated
schemes and `Λ` a ring, in an arbitrary universe `Type r`. For a compactification `j : X ⟶ X̄`
of `X` over `Y` the functor `Rf_! = R(j̄)_* ∘ j_!` of [Stacks, Tag 0F7H] is
`Stacks.EtaleCohomology.derivedLowerShriek`, on bounded below derived categories, and
`Stacks.EtaleCohomology.derivedLowerShriekUnbounded`, on unbounded ones.
[Stacks, Tag 0F7I] says that these functors are, up to canonical isomorphism, independent of
the compactification: on `D⁺_tors(X_étale, Λ)` for every ring `Λ`, and on `D(X_étale, Λ)` for a
torsion ring `Λ`.

The proof is the source's. Compactifications exist (Tag 0F41) and form a cofiltered category
(Tag 0ATU, `Stacks.EtaleCohomology.isCofiltered_compactificationOf`). A morphism `g : j ⟶ k` of
compactifications induces the isomorphism
`Stacks.EtaleCohomology.derivedLowerShriekHomIsoUniv`, built from the map of Tag 0F7G, and these
isomorphisms compose (`Stacks.EtaleCohomology.derivedLowerShriekHomIsoUniv_comp`). Hence any two
compactifications are compared through a third mapping to both, and by the footnote of the
source the comparison does not depend on the third
(`CategoryTheory.IsCofiltered.isoSystemComparison`).

## Main definitions

* `Stacks.EtaleCohomology.derivedLowerShriekCompactificationIsoUniv`: the canonical isomorphism
  between the derived lower shriek functors on `D⁺_tors(X_étale, Λ)` of two compactifications.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompactificationIsoUniv`: the same on
  `D(X_étale, Λ)` for a torsion ring `Λ`.

## Main results

* `Stacks.EtaleCohomology.derivedLowerShriek_independent_of_compactification_univ`:
  **[Stacks, Tag 0F7I]** for `Rf_! : D⁺_tors(X_étale, Λ) ⥤ D⁺_tors(Y_étale, Λ)`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnbounded_independent_of_compactification_univ`:
  **[Stacks, Tag 0F7I]** for `Rf_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)`, `Λ` a torsion ring.

The two registered statements cover the two functors of the source: the source proves the
second and says the first "is proved in exactly the same way".

## Implementation notes

The coefficient ring is an arbitrary ring `Λ : Type r`, not necessarily commutative, and the
sheaves are those of `Stacks.EtaleCohomology.EtaleModules.{u, r}`, the setting of the functors
`Rf_!` of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology`. The proper
base change theorem, proved for abelian sheaves with coefficients in `AddCommGrpCat.{u + 1}`,
enters at the coefficients `AddCommGrpCat.{max (u + 1) r}` through
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.CoefficientUniverse`.
A torsion ring is one in which `m • 1 = 0` for some `m > 0`.

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

universe u r

namespace Stacks.EtaleCohomology

/- `etaleModules_enoughInjectives_univZero` is stated for the coefficient ring in `Type`; instance
search would try to unify an arbitrary coefficient universe with it and fail on the universe
constraint, so it is switched off here. -/
attribute [-instance] etaleModules_enoughInjectives_univZero

attribute [local instance 2000] etaleModules_enoughInjectives

attribute [local instance] HasDerivedCategory.standard

/-- **The canonical isomorphism between `Rf_!` computed through two compactifications**, on
`D⁺_tors(X_étale, Λ)`: through any compactification `l` mapping to both, it is
`Rf_!^{j₁} ≅ Rf_!^l ≅ Rf_!^{j₂}`, the isomorphisms being those of the two morphisms of
compactifications (`Stacks.EtaleCohomology.derivedLowerShriekHomIsoUniv`). -/
def derivedLowerShriekCompactificationIsoUniv {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y]
    [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
    (j₁ j₂ : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ] :
    (isTorsionPlus.{u, r} Λ X).ι ⋙ derivedLowerShriek.{u, r} f j₁ Λ ≅
      (isTorsionPlus.{u, r} Λ X).ι ⋙ derivedLowerShriek.{u, r} f j₂ Λ :=
  IsCofiltered.isoSystemComparison
    (Φ := fun j => (isTorsionPlus.{u, r} Λ X).ι ⋙ derivedLowerShriek.{u, r} f j Λ)
    (fun g => derivedLowerShriekHomIsoUniv Λ g) j₁ j₂

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f]
  [LocallyOfFiniteType f] [QuasiCompact f] (Λ : Type r) [Ring Λ]

/-- The comparisons of `Stacks.EtaleCohomology.derivedLowerShriekCompactificationIsoUniv`
compose. -/
theorem derivedLowerShriekCompactificationIsoUniv_trans (j k l : CompactificationOf (Over.mk f)) :
    derivedLowerShriekCompactificationIsoUniv f j k Λ ≪≫
        derivedLowerShriekCompactificationIsoUniv f k l Λ =
      derivedLowerShriekCompactificationIsoUniv f j l Λ :=
  IsCofiltered.isoSystemComparison_trans _ (fun g h => derivedLowerShriekHomIsoUniv_comp Λ g h)
    j k l

/-- Along a morphism `g : j ⟶ k` of compactifications the comparison
`Rf_!^k ≅ Rf_!^j` is the isomorphism `Stacks.EtaleCohomology.derivedLowerShriekHomIsoUniv` of `g`,
built from the map of [Stacks, Tag 0F7G]. -/
theorem derivedLowerShriekCompactificationIsoUniv_of_hom {j k : CompactificationOf (Over.mk f)}
    (g : j ⟶ k) :
    derivedLowerShriekCompactificationIsoUniv f k j Λ = derivedLowerShriekHomIsoUniv Λ g :=
  IsCofiltered.isoSystemComparison_of_hom _ (fun g h => derivedLowerShriekHomIsoUniv_comp Λ g h) g

/-- **Stacks Project, Tag 0F7I**, for `Rf_! : D⁺_tors(X_étale, Λ) ⥤ D⁺_tors(Y_étale, Λ)` and an
arbitrary ring `Λ`. Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact and
quasi-separated schemes. Then `X` has a compactification over `Y`, and the functors `Rf_!`
built from the compactifications are, up to canonical isomorphism, independent of the
compactification: the isomorphisms `derivedLowerShriekCompactificationIsoUniv f j k Λ` between them
compose, and along every morphism `g : j ⟶ k` of compactifications they are the isomorphism
built from the map of [Stacks, Tag 0F7G] and the composition of derived direct images. -/
@[stacks 0F7I "bounded-below torsion complexes, arbitrary ring Λ in any universe",
  sga "4½ Arcata 4.5.3" "more general",
  sga "7 XIII 2.1.6" "more general"]
theorem derivedLowerShriek_independent_of_compactification_univ :
    (∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion) ∧
      (∀ j k l : CompactificationOf (Over.mk f),
        derivedLowerShriekCompactificationIsoUniv f j k Λ ≪≫
            derivedLowerShriekCompactificationIsoUniv f k l Λ =
          derivedLowerShriekCompactificationIsoUniv f j l Λ) ∧
      ∀ {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k),
        derivedLowerShriekCompactificationIsoUniv f k j Λ = derivedLowerShriekHomIsoUniv Λ g :=
  ⟨hasCompactification_of_compactSpace_quasiSeparatedSpace f,
    derivedLowerShriekCompactificationIsoUniv_trans f Λ,
    fun g => derivedLowerShriekCompactificationIsoUniv_of_hom f Λ g⟩

/-! ### The unbounded derived category, for a torsion ring -/

/-- **The canonical isomorphism between `Rf_!` computed through two compactifications**, on
`D(X_étale, Λ)` for a torsion ring `Λ`. -/
def derivedLowerShriekUnboundedCompactificationIsoUniv {X Y : Scheme.{u}} (f : X ⟶ Y)
    [CompactSpace Y] [QuasiSeparatedSpace Y] [IsSeparated f] [LocallyOfFiniteType f]
    [QuasiCompact f] (j₁ j₂ : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0) :
    derivedLowerShriekUnbounded.{u, r} f j₁ Λ ≅ derivedLowerShriekUnbounded.{u, r} f j₂ Λ :=
  IsCofiltered.isoSystemComparison
    (Φ := fun j => derivedLowerShriekUnbounded.{u, r} f j Λ)
    (fun g => derivedLowerShriekUnboundedHomIsoUniv Λ g hΛ) j₁ j₂

variable (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-- The comparisons of `derivedLowerShriekUnboundedCompactificationIsoUniv` compose. -/
@[sga "4 XVII 3.3.2.1" "special case"]
theorem derivedLowerShriekUnboundedCompactificationIsoUniv_trans
    (j k l : CompactificationOf (Over.mk f)) :
    derivedLowerShriekUnboundedCompactificationIsoUniv f j k Λ hΛ ≪≫
        derivedLowerShriekUnboundedCompactificationIsoUniv f k l Λ hΛ =
      derivedLowerShriekUnboundedCompactificationIsoUniv f j l Λ hΛ :=
  IsCofiltered.isoSystemComparison_trans _
    (fun g h => derivedLowerShriekUnboundedHomIsoUniv_comp Λ g h hΛ) j k l

/-- Along a morphism `g : j ⟶ k` of compactifications the comparison is the isomorphism
`Stacks.EtaleCohomology.derivedLowerShriekUnboundedHomIsoUniv` of `g`. -/
theorem derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom
    {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k) :
    derivedLowerShriekUnboundedCompactificationIsoUniv f k j Λ hΛ =
      derivedLowerShriekUnboundedHomIsoUniv Λ g hΛ :=
  IsCofiltered.isoSystemComparison_of_hom _
    (fun g h => derivedLowerShriekUnboundedHomIsoUniv_comp Λ g h hΛ) g

/-- **Stacks Project, Tag 0F7I**, for `Rf_! : D(X_étale, Λ) ⥤ D(Y_étale, Λ)` and a torsion ring
`Λ`. Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact and quasi-separated
schemes. Then `X` has a compactification over `Y`, and the functors `Rf_!` built from the
compactifications are, up to canonical isomorphism, independent of the compactification: the
isomorphisms `derivedLowerShriekUnboundedCompactificationIsoUniv f j k Λ hΛ` between them compose,
and along every morphism `g : j ⟶ k` of compactifications they are the isomorphism built from
the map of [Stacks, Tag 0F7G] and the composition of derived direct images. -/
@[stacks 0F7I "unbounded derived category D(X_étale, Λ), Λ a torsion ring in any universe",
  sga "4 XVII 5.2.2" "special case",
  sga "4½ Arcata 4.5.3" "more general",
  sga "7 XIII 2.1.6" "more general"]
theorem derivedLowerShriekUnbounded_independent_of_compactification_univ :
    (∃ j : CompactificationOf (Over.mk f), QuasiCompact j.immersion) ∧
      (∀ j k l : CompactificationOf (Over.mk f),
        derivedLowerShriekUnboundedCompactificationIsoUniv f j k Λ hΛ ≪≫
            derivedLowerShriekUnboundedCompactificationIsoUniv f k l Λ hΛ =
          derivedLowerShriekUnboundedCompactificationIsoUniv f j l Λ hΛ) ∧
      ∀ {j k : CompactificationOf (Over.mk f)} (g : j ⟶ k),
        derivedLowerShriekUnboundedCompactificationIsoUniv f k j Λ hΛ =
          derivedLowerShriekUnboundedHomIsoUniv Λ g hΛ :=
  ⟨hasCompactification_of_compactSpace_quasiSeparatedSpace f,
    derivedLowerShriekUnboundedCompactificationIsoUniv_trans f Λ hΛ,
    fun g => derivedLowerShriekUnboundedCompactificationIsoUniv_of_hom f Λ hΛ g⟩

end Stacks.EtaleCohomology
