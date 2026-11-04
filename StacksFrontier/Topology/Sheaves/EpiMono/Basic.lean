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

Here a "surjective map of presheaves" means a map that is surjective on every open
set (equivalently, the underlying natural transformation is componentwise surjective),
and similarly for injective.  For sheaves, the canonical Stacks Project notion of a
"surjective map of sheaves" is one whose induced maps on all stalks are surjective
(see Stacks tag 008Q); the Stacks notion of "injective map of sheaves" is one whose
induced maps on every open set are injective, which by part (2) below is equivalent to
injectivity on all stalks.

The formalization below works with sheaves and presheaves of types on a bundled
topological space `X : TopCat.{u}`.

The four iff statements are bundled at the end as `StacksDefinitionInjective`.
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

The Stacks notion of "injective map of sheaves" is "injective on every open set", and the
Stacks notion of "surjective map of sheaves" is "surjective on every stalk"
(cf. Stacks tag 008Q).  With those Stacks definitions, the two parts above show that
in `Sh(X)` the epimorphisms are exactly the surjective maps of sheaves and the
monomorphisms are exactly the injective maps of sheaves.
-/
@[stacks 0H7H,
  sga "4 IV 6.4.3" "sheaves on a space",
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
