module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleModuleDerivedFunctors
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.Compactifications
import StacksCore.Tactic.StacksAttribute

/-!
# Compactly supported cohomology

Let `f : X ⟶ Y` be a finite type separated morphism of schemes and let `Λ` be a ring.  Choosing
a compactification `j : X ⟶ Xbar` of `X` over `Y`, so an open immersion into a scheme proper
over `Y`, the derived lower shriek functor is `Rf_! = R(fbar)_* ∘ j_!`.  For `Y = Spec k` the
cohomology of `K` with compact support is `RΓ_c(X, K) = RΓ(Spec k, Rf_! K)`, and
`H^i_c(X, K) = H^i(RΓ_c(X, K))`.

## Main definitions

* `Stacks.EtaleCohomology.IsTorsionEtaleModule`: a sheaf of modules on the small étale site is
  torsion when its sections are locally annihilated by positive integers.
* `Stacks.EtaleCohomology.derivedLowerShriek`: the functor `Rf_!` attached to a
  compactification.
* `Stacks.EtaleCohomology.compactlySupportedCohomology` and
  `Stacks.EtaleCohomology.compactlySupportedCohomologyTorsion`: the complex `RΓ_c(X, K)`, on
  bounded below objects and on the bounded below objects with torsion cohomology sheaves.
* `Stacks.EtaleCohomology.compactlySupportedCohomologyGroup`: the module `H^i_c(X, K)`.

## Implementation notes

A compactification `AlgebraicGeometry.CompactificationOf`, an open immersion of `X` into a
scheme proper over the base, is an explicit argument rather than a choice. Stacks Tag 0F7I, that
different compactifications give canonically isomorphic functors, is not proved here, so the
dependence of these definitions on the chosen compactification is visible in their arguments.

The source states the definition for `K` in the bounded below derived category with torsion
cohomology sheaves, and for a torsion ring `Λ` on the whole derived category.  The formula uses
neither hypothesis, so `Stacks.EtaleCohomology.compactlySupportedCohomology` is given on the
whole bounded below derived category and `compactlySupportedCohomologyTorsion` is its
restriction to the subcategory of the source.

## References

* [Stacks Project, Tag 0F7H](https://stacks.math.columbia.edu/tag/0F7H)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
* [Stacks Project, Tag 0GJZ](https://stacks.math.columbia.edu/tag/0GJZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe u r

namespace Stacks.EtaleCohomology

/-! ### Derived lower shriek through a compactification -/

/-- **Stacks Project, Tag 0F7H.** The derived lower shriek functor `Rf_! = R(fbar)_* ∘ j_!`
attached to a compactification `j : X ⟶ Xbar` of `X` over `Y`, on bounded below derived
categories of sheaves of `Λ`-modules for the small étale topologies. -/
abbrev derivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ] :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ Y) :=
  etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion ⋙
    etaleModuleDerivedDirectImage.{u, r} Λ j.toBase

/-! ### Torsion sheaves of modules -/

/-- A sheaf of `Λ`-modules on the small étale site of `X` is torsion when every section over an
object of the site is, on the members of some covering sieve, annihilated by a positive
integer. -/
def IsTorsionEtaleModule (Λ : Type r) [Ring Λ] (X : Scheme.{u})
    (F : EtaleModules.{u, r} Λ X) : Prop :=
  ∀ (V : X.Etale) (x : F.obj.obj (op V)), ∃ R : Sieve V, R ∈ X.smallEtaleTopology V ∧
    ∀ (W : X.Etale) (g : W ⟶ V), R g → ∃ n : ℕ, 0 < n ∧ n • F.obj.map g.op x = 0

/-- The objects of the bounded below derived category of sheaves of `Λ`-modules on the small
étale site of `X` all of whose cohomology sheaves are torsion.  This is the subcategory
`D⁺_tors(X_étale, Λ)` of the source. -/
@[sga "4 XVII 5.1.13" "special case"]
def isTorsionPlus (Λ : Type r) [Ring Λ] (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory.Plus (EtaleModules.{u, r} Λ X)) :=
  fun K ↦ ∀ i : ℤ, IsTorsionEtaleModule.{u, r} Λ X
    ((DerivedCategory.Plus.homologyFunctor (EtaleModules.{u, r} Λ X) i).obj K)

/-! ### Cohomology with compact support -/

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]

/-- **Stacks Project, Tag 0GJZ.** The cohomology with compact support
`RΓ_c(X, K) = RΓ(Spec k, Rf_! K)` of a bounded below complex of sheaves of `Λ`-modules on the
small étale site of a separated finite type `k`-scheme `X`, through a compactification `j`. -/
@[stacks 0GJZ "RΓ_c(X, K) = RΓ(Spec k, Rf_! K)", sga "7 XXII 3.4"]
abbrev compactlySupportedCohomology (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ] :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ X) ⥤
      DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  derivedLowerShriek.{u, r} f j Λ ⋙ etaleModuleDerivedGlobalSections.{u, r} Λ (Spec (.of k))

/-- **Stacks Project, Tag 0GJZ.** Cohomology with compact support on the subcategory
`D⁺_tors(X_étale, Λ)` of bounded below complexes with torsion cohomology sheaves, which is the
domain the source states the definition on. -/
@[stacks 0GJZ "RΓ_c on D⁺_tors"]
abbrev compactlySupportedCohomologyTorsion (j : CompactificationOf (Over.mk f))
    (Λ : Type r) [Ring Λ] :
    (isTorsionPlus.{u, r} Λ X).FullSubcategory ⥤
      DerivedCategory.Plus (ModuleCat.{max (u + 1) r} Λ) :=
  (isTorsionPlus.{u, r} Λ X).ι ⋙ compactlySupportedCohomology.{u, r} k f j Λ

/-- **Stacks Project, Tag 0GJZ.** The compactly supported cohomology module
`H^i_c(X, K) = H^i(RΓ_c(X, K))`. -/
@[stacks 0GJZ "H^i_c(X, K) = H^i(RΓ_c(X, K))"]
abbrev compactlySupportedCohomologyGroup (j : CompactificationOf (Over.mk f))
    (Λ : Type r) [Ring Λ] (i : ℤ) :
    DerivedCategory.Plus (EtaleModules.{u, r} Λ X) ⥤ ModuleCat.{max (u + 1) r} Λ :=
  compactlySupportedCohomology.{u, r} k f j Λ ⋙
    DerivedCategory.Plus.homologyFunctor (ModuleCat.{max (u + 1) r} Λ) i

end Stacks.EtaleCohomology

end
