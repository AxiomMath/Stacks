module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsOverAnOpen
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.SectionsWithSupport

/-!
# Sections over an open of a ringed space, with the global scalars, and their derived functors

On a ringed space `X` the functor `Stacks.Cohomology.SectionsWithSupport.sectionsOnComplement`
takes a sheaf of modules to its sections over the complement of a closed subset, regarded as a
module over the ring `Γ(X, 𝒪_X)` of *global* functions: it is evaluation over that open followed
by restriction of scalars along `Γ(X, 𝒪_X) → Γ(U, 𝒪_X)`.  This file isolates that construction
for an arbitrary open and pulls the restriction of scalars out of its right derived functors.

## Main definitions

* `Stacks.Cohomology.ModuleComparison.sectionsOnOpen` — sections over an arbitrary open with
  scalars restricted to the global functions.  `sectionsOnComplement X Z hZ` is its value at the
  open complement of `Z`, definitionally.

## Main results

* `Stacks.Cohomology.ModuleComparison.sectionsOnOpenDerivedIso` — deriving the module-valued
  sections over the open and then restricting scalars agrees with deriving
  `sectionsOnOpen`, naturally in the sheaf of modules.
* `Stacks.Cohomology.ModuleComparison.sectionsOnComplementDerivedIso` — the same statement for
  `sectionsOnComplement`.

## Implementation notes

The content is `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`: an exact additive
functor commutes with right derived functors.  Here the exact functor is
`ModuleCat.restrictScalars` along the restriction map of the structure sheaf, and the
comparison it is applied to is the identity, because `sectionsOnOpen` *is* the composite —
`Iso.refl` suffices.

Mathlib's exactness instances for `ModuleCat.restrictScalars` are stated for a homomorphism of
*commutative* rings, while the structure sheaf of a ringed space enters the `SheafOfModules` API
through `RingCat`, so they do not apply.  The two instances are therefore recorded here for a
homomorphism of arbitrary rings; the proof is Mathlib's, namely that exactness of a short complex
of modules is a statement about the underlying additive maps
(`CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact`), which restriction
of scalars does not change.  They are `local` so that no instance of that shape leaks to
importers.

The target category `Stacks.Cohomology.SectionsWithSupport.GlobalModules X` of `sectionsOnOpen`
does not mention the open.  That is what makes the open an ordinary argument that may be rewritten
later without transporting any module structure, and it is why `sectionsOnOpen` is introduced
rather than used inline.

## References

* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.SectionsWithSupport
open RingedSpaceModuleAdjunction

universe v u u'

namespace Stacks.Cohomology.ModuleComparison

/-! ### Restriction of scalars along a homomorphism of arbitrary rings is exact -/

/-- **Restriction of scalars is exact**, for a homomorphism of not necessarily commutative
rings.  Exactness of a short complex of modules says that the underlying sequence of additive
maps is exact, and restriction of scalars leaves those maps alone. -/
theorem restrictScalars_map_exact {R : Type u} [Ring R] {S : Type u'} [Ring S] (f : R →+* S)
    (T : ShortComplex (ModuleCat.{v} S)) (hT : T.Exact) :
    (T.map (ModuleCat.restrictScalars.{v} f)).Exact := by
  rwa [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢

/-- Restriction of scalars along a homomorphism of arbitrary rings is left exact. -/
local instance restrictScalars_preservesFiniteLimits {R : Type u} [Ring R] {S : Type u'} [Ring S]
    (f : R →+* S) : PreservesFiniteLimits (ModuleCat.restrictScalars.{v} f) := by
  have h := ((Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 2 4).mp
    (restrictScalars_map_exact f)
  exact h.1

/-- Restriction of scalars along a homomorphism of arbitrary rings is right exact. -/
local instance restrictScalars_preservesFiniteColimits {R : Type u} [Ring R] {S : Type u'}
    [Ring S] (f : R →+* S) : PreservesFiniteColimits (ModuleCat.restrictScalars.{v} f) := by
  have h := ((Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 2 4).mp
    (restrictScalars_map_exact f)
  exact h.2

/-! ### Sections over an open, with the global scalars -/

variable (X : RingedSpace.{u, u})

/-- **Sections over an open of a ringed space, as a module over the global functions.** The
sections of a sheaf of `𝒪_X`-modules over `W`, with scalars restricted along the restriction map
`Γ(X, 𝒪_X) → Γ(W, 𝒪_X)`.

The target does not depend on `W`, so varying the open is an ordinary rewrite. -/
public noncomputable def sectionsOnOpen (W : Opens X) : ModuleSheaves X ⥤ GlobalModules X :=
  SheafOfModules.evaluation (structureSheafRing X) (op W) ⋙
    ModuleCat.restrictScalars
      ((structureSheafRing X).obj.map (homOfLE (le_top : W ≤ ⊤)).op).hom

/-- Sections over an open, with the global scalars, form an additive functor. -/
public instance sectionsOnOpen_additive (W : Opens X) : (sectionsOnOpen X W).Additive where
  map_add := rfl

/-- Sections over the complement of a closed subset are the sections over that open. -/
public theorem sectionsOnComplement_eq (Z : Set X) (hZ : IsClosed Z) :
    sectionsOnComplement X Z hZ = sectionsOnOpen X (openComplement Z hZ) :=
  rfl

/-! ### The derived comparison -/

/-- **Restriction of scalars passes through the derived sections over an open.** Deriving the
module-valued sections over `W` and then reading the result over the global functions agrees with
deriving `sectionsOnOpen`, naturally in the sheaf of modules.

Restriction of scalars is exact, so this is
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso` applied to the identity comparison:
`sectionsOnOpen X W` is the composite on the nose. -/
public noncomputable def sectionsOnOpenDerivedIso (W : Opens X) (p : ℕ) :
    (SheafOfModules.evaluation (structureSheafRing X)
          (op W)).rightDerived p ⋙
        ModuleCat.restrictScalars
          ((structureSheafRing X).obj.map
            (homOfLE (le_top : W ≤ ⊤)).op).hom ≅
      (sectionsOnOpen X W).rightDerived p :=
  rightDerivedCompIso _ _ _ (Iso.refl _) p

/-- **Restriction of scalars passes through the derived sections on the complement of a closed
subset**: the instance of `sectionsOnOpenDerivedIso` at the open complement. -/
public noncomputable def sectionsOnComplementDerivedIso (Z : Set X) (hZ : IsClosed Z) (p : ℕ) :
    (SheafOfModules.evaluation (structureSheafRing X)
          (op (openComplement Z hZ))).rightDerived p ⋙
        ModuleCat.restrictScalars
          ((structureSheafRing X).obj.map
            (homOfLE (le_top : openComplement Z hZ ≤ ⊤)).op).hom ≅
      (sectionsOnComplement X Z hZ).rightDerived p :=
  sectionsOnOpenDerivedIso X (openComplement Z hZ) p

end Stacks.Cohomology.ModuleComparison

end
