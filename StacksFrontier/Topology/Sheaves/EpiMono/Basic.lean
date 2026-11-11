module

public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.Types.Pushouts
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.LocallySurjective
public import StacksFrontier.Topology.Sheaves.EpiMono.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks tag 0H7H — Characterization of epimorphisms and monomorphisms of (pre)sheaves

Let `X` be a topological space.

1. Epimorphisms (resp. monomorphisms) in the category of presheaves are exactly the
   surjective (resp. injective) maps of presheaves.
2. Epimorphisms (resp. monomorphisms) in the category of sheaves are exactly the
   surjective (resp. injective) maps of sheaves, and are exactly those maps which are
   surjective (resp. injective) on all the stalks.

The words are those of Stacks tag 007U: a map of presheaves of sets is injective
(resp. surjective) if it is injective (resp. surjective) on every open set (007U (2), (3));
a map of sheaves of sets is injective if it is injective on every open set (007U (4)), and
surjective if every section is locally in the image (007U (5)), which is
`TopCat.Presheaf.IsLocallySurjective` (see
`SheafInjectiveSurjective.isLocallySurjective_iff_exists_cover`).

The formalization below works with sheaves and presheaves of types on a bundled
topological space `X : TopCat.{u}`.

The complete statement is `presheaf_sheaf_epi_mono_iff_surjective_injective`, which carries
the tag; `StacksDefinitionInjective` is the earlier bundle without the clause "epimorphisms
of sheaves are the surjective maps of sheaves".
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopCat
open SheafInjectiveSurjective (presheaf_mono_iff_injective presheaf_epi_iff_surjective)

universe u

variable {X : TopCat.{u}}

/-! ## Part (1): presheaves

Clauses (1) are `SheafInjectiveSurjective.presheaf_mono_iff_injective` and
`SheafInjectiveSurjective.presheaf_epi_iff_surjective`, opened above: tag 007U (2)-(3) states
exactly the two presheaf clauses of this tag, so they are used here rather than restated. -/

/-! ## Part (2): sheaves -/

/-- **Stacks 0H7H (2), monomorphism / injective on opens.**  A morphism of sheaves
of types is a monomorphism if and only if every component `f.1.app U` is injective. -/
theorem sheaf_mono_iff_app_injective {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G) :
    Mono f ↔ ∀ U : (Opens X)ᵒᵖ, Function.Injective (f.1.app U) := by
  refine (CategoryTheory.Sheaf.Hom.mono_iff_presheaf_mono
      (Opens.grothendieckTopology X) (Type u) f).trans ?_
  exact presheaf_mono_iff_injective f.1

/-- **Stacks 0H7H (2), monomorphism / injective on stalks.**  A morphism of sheaves
of types is a monomorphism if and only if it is injective on every stalk. -/
@[sga "4 IV 6.4.3" "special case", sga "4 IV 8.4.1"]
theorem sheaf_mono_iff_stalk_injective {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G) :
    Mono f ↔ ∀ x : X, Function.Injective ((TopCat.Presheaf.stalkFunctor (Type u) x).map f.1) := by
  refine (TopCat.Presheaf.mono_iff_stalk_mono f).trans ?_
  refine forall_congr' (fun x => ?_)
  exact CategoryTheory.mono_iff_injective _

/-- **Stacks 0H7H (2), epimorphism / surjective map of sheaves.**  A morphism of sheaves of
types is an epimorphism if and only if it is surjective in the sense of Stacks 007U (5), i.e.
locally surjective. -/
theorem sheaf_epi_iff_isLocallySurjective {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G) :
    Epi f ↔ TopCat.Presheaf.IsLocallySurjective f.1 :=
  (TopCat.Sheaf.isLocallySurjective_iff_epi f).symm

/-- **Stacks 0H7H (2), epimorphism / surjective on stalks.**  A morphism of sheaves
of types is an epimorphism if and only if it is surjective on every stalk.

This combines `TopCat.Sheaf.isLocallySurjective_iff_epi` (epi iff locally surjective)
with `TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks` (locally surjective
iff surjective on stalks). -/
@[sga "4 IV 6.4.3" "special case"]
theorem sheaf_epi_iff_stalk_surjective {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G) :
    Epi f ↔ ∀ x : X, Function.Surjective ((TopCat.Presheaf.stalkFunctor (Type u) x).map f.1) := by
  rw [← TopCat.Sheaf.isLocallySurjective_iff_epi]
  exact TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks f.1

/-! ## Full bundled statement of tag 0H7H -/

/--
**Stacks 0H7H, full statement.**

Let `X : TopCat`.

1. For a morphism `f : F ⟶ G` of presheaves of types on `X`:
   - `f` is a monomorphism iff each component `f.app U` is injective;
   - `f` is an epimorphism iff each component `f.app U` is surjective.
2. For a morphism `f : F ⟶ G` of sheaves of types on `X`:
   - `f` is a monomorphism iff each component `f.1.app U` is injective,
     iff `f` is injective on every stalk;
   - `f` is an epimorphism iff `f` is surjective on every stalk.

The Stacks notion of "injective map of sheaves" is "injective on every open set"
(Stacks 007U (4)), so the third conjunct says the monomorphisms of sheaves are the injective
maps of sheaves.  The Stacks notion of "surjective map of sheaves" is "locally surjective"
(Stacks 007U (5)), not "surjective on every stalk"; the clause that the epimorphisms of
sheaves are the surjective maps of sheaves is not among these conjuncts.  The complete
statement of Stacks 0H7H, with that clause, is
`presheaf_sheaf_epi_mono_iff_surjective_injective`.
-/
@[sga "4 IV 6.4.3" "sheaves on a space",
  sga "3 I 1.2" "special case",
  sga "4 IV 8.4.1" "fourth conjunct"]
theorem StacksDefinitionInjective :
    -- Part (1): presheaves
    (∀ {F G : TopCat.Presheaf (Type u) X} (f : F ⟶ G),
        Mono f ↔ ∀ U : (Opens X)ᵒᵖ, Function.Injective (f.app U)) ∧
    (∀ {F G : TopCat.Presheaf (Type u) X} (f : F ⟶ G),
        Epi f ↔ ∀ U : (Opens X)ᵒᵖ, Function.Surjective (f.app U)) ∧
    -- Part (2): sheaves
    (∀ {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G),
        Mono f ↔ ∀ U : (Opens X)ᵒᵖ, Function.Injective (f.1.app U)) ∧
    (∀ {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G),
        Mono f ↔ ∀ x : X,
          Function.Injective ((TopCat.Presheaf.stalkFunctor (Type u) x).map f.1)) ∧
    (∀ {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G),
        Epi f ↔ ∀ x : X,
          Function.Surjective ((TopCat.Presheaf.stalkFunctor (Type u) x).map f.1)) :=
  ⟨@presheaf_mono_iff_injective X,
   @presheaf_epi_iff_surjective X,
   @sheaf_mono_iff_app_injective X,
   @sheaf_mono_iff_stalk_injective X,
   @sheaf_epi_iff_stalk_surjective X⟩

/--
**Stacks 0H7H.** Let `X : TopCat`.

1. A morphism `f : F ⟶ G` of presheaves of types on `X` is a monomorphism (resp. an
   epimorphism) iff it is injective (resp. surjective) on every open set, i.e. iff it is an
   injective (resp. surjective) map of presheaves (Stacks 007U (2), (3)).
2. A morphism `f : F ⟶ G` of sheaves of types on `X`
   - is a monomorphism iff it is injective on every open set (an injective map of sheaves,
     Stacks 007U (4)), iff it is injective on every stalk;
   - is an epimorphism iff it is locally surjective (a surjective map of sheaves,
     Stacks 007U (5); `TopCat.Presheaf.IsLocallySurjective` is that notion by
     `SheafInjectiveSurjective.isLocallySurjective_iff_exists_cover`), iff it is surjective
     on every stalk.
-/
@[stacks 0H7H]
theorem presheaf_sheaf_epi_mono_iff_surjective_injective :
    -- Part (1): presheaves
    (∀ {F G : TopCat.Presheaf (Type u) X} (f : F ⟶ G),
        Mono f ↔ ∀ U : (Opens X)ᵒᵖ, Function.Injective (f.app U)) ∧
    (∀ {F G : TopCat.Presheaf (Type u) X} (f : F ⟶ G),
        Epi f ↔ ∀ U : (Opens X)ᵒᵖ, Function.Surjective (f.app U)) ∧
    -- Part (2): sheaves
    (∀ {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G),
        Mono f ↔ ∀ U : (Opens X)ᵒᵖ, Function.Injective (f.1.app U)) ∧
    (∀ {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G),
        Mono f ↔ ∀ x : X,
          Function.Injective ((TopCat.Presheaf.stalkFunctor (Type u) x).map f.1)) ∧
    (∀ {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G),
        Epi f ↔ TopCat.Presheaf.IsLocallySurjective f.1) ∧
    (∀ {F G : TopCat.Sheaf (Type u) X} (f : F ⟶ G),
        Epi f ↔ ∀ x : X,
          Function.Surjective ((TopCat.Presheaf.stalkFunctor (Type u) x).map f.1)) :=
  ⟨@presheaf_mono_iff_injective X,
   @presheaf_epi_iff_surjective X,
   @sheaf_mono_iff_app_injective X,
   @sheaf_mono_iff_stalk_injective X,
   @sheaf_epi_iff_isLocallySurjective X,
   @sheaf_epi_iff_stalk_surjective X⟩
