module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.ShortExact
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.FlatModuleSheavesAndStalks
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.LinearEquiv
public import StacksCore.Tactic.StacksAttribute

/-!
# Weakly associated points: comparisons and inclusions

For a sheaf of modules on a scheme, the associated points are weakly associated, the weakly
associated points lie in the support, and the two notions agree at any point whose local ring
has a finitely generated maximal ideal — in particular everywhere on a locally Noetherian
scheme. Weakly associated points also behave well in a short exact sequence.

## Main results

* `AlgebraicGeometry.associatedPoints_subset_weaklyAssociatedPoints` and
  `AlgebraicGeometry.weaklyAssociatedPoints_subset_supp`: `Ass(F) ⊆ WeakAss(F) ⊆ Supp(F)`.
* `AlgebraicGeometry.weaklyAssociatedPoints_subset_of_shortExact` and
  `AlgebraicGeometry.weaklyAssociatedPoints_subset_union_of_shortExact`: the behaviour of weakly
  associated points in a short exact sequence.
* `AlgebraicGeometry.mem_associatedPoints_iff_mem_weaklyAssociatedPoints` and
  `AlgebraicGeometry.associatedPoints_eq_weaklyAssociatedPoints`: the two notions agree over a
  finitely generated maximal ideal, hence on a locally Noetherian scheme.

## Implementation notes

The source assumes quasi-coherence throughout, but only the subsheaf inclusion uses it: the
remaining arguments are statements about the stalks, where exactness of the stalk functor and
the corresponding module-theoretic results suffice. They are therefore stated for every sheaf
of modules.

A short exact sequence is a `CategoryTheory.ShortComplex` together with its `ShortExact`
property, and the induced short exact sequence of stalks is
  `Stacks.SheafOfModules.FlatShortExact.stalkShortExact`.

## References

* [Stacks Project, Tag 05AM](https://stacks.math.columbia.edu/tag/05AM)
* [Stacks Project, Tag 05AN](https://stacks.math.columbia.edu/tag/05AN)
* [Stacks Project, Tag 05AR](https://stacks.math.columbia.edu/tag/05AR)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 05AM.** Every associated point of a sheaf of modules is weakly
associated. -/
@[stacks 05AM "associated points"]
lemma associatedPoints_subset_weaklyAssociatedPoints {X : Scheme.{u}} (F : X.Modules) :
    Stacks.Divisors.associatedPoints F ⊆ Stacks.Divisors.weaklyAssociatedPoints F :=
  Stacks.Divisors.associatedPoints_subset F

/-- **Stacks Project, Tag 05AM.** Every weakly associated point of a sheaf of modules belongs
to its support. -/
@[stacks 05AM "weakly associated points"]
lemma weaklyAssociatedPoints_subset_supp {X : Scheme.{u}} (F : X.Modules) :
    Stacks.Divisors.weaklyAssociatedPoints F ⊆ SheafOfModules.supp F := fun x hx =>
  (SheafOfModules.mem_supp_iff_nontrivial_stalk
    (show SheafOfModules X.ringCatSheaf from F) x).mpr hx.nontrivial

/-- **Stacks Project, Tag 05AN.** In a short exact sequence of quasi-coherent modules on a
scheme, the weakly associated points of the first module are weakly associated points of the
middle module. -/
@[stacks 05AN "subsheaf_inclusion"]
theorem weaklyAssociatedPoints_subset_of_shortExact {X : Scheme.{u}}
    (S : ShortComplex X.Modules) [S.X₁.IsQuasicoherent] [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] (hS : S.ShortExact) :
    Stacks.Divisors.weaklyAssociatedPoints S.X₁ ⊆ Stacks.Divisors.weaklyAssociatedPoints S.X₂ :=
  fun x hx => Module.weaklyAssociatedPrimes_subset_of_injective
    (f := OXModule.stalkLinearMap S.X₁ S.X₂ S.f x)
    (@OXModule.stalkMapAdd_injective_of_mono _ S.X₁ S.X₂ S.f hS.mono_f x) hx

/-- **Stacks Project, Tag 05AN.** In a short exact sequence of sheaves of modules, every weakly
associated point of the middle term is weakly associated to an outer term. -/
@[stacks 05AN "middle_term_inclusion"]
theorem weaklyAssociatedPoints_subset_union_of_shortExact {X : Scheme.{u}}
    (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    Stacks.Divisors.weaklyAssociatedPoints S.X₂ ⊆
      Stacks.Divisors.weaklyAssociatedPoints S.X₁ ∪
        Stacks.Divisors.weaklyAssociatedPoints S.X₃ := by
  intro x hx
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule S.X₁ x
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule S.X₂ x
  let := Stacks.SheafOfModules.FlatShortExact.stalkModule S.X₃ x
  obtain ⟨f, g, hf, hfg, -⟩ := Stacks.SheafOfModules.FlatShortExact.stalkShortExact S hS x
  exact Module.weaklyAssociatedPrimes_subset_union_of_exact hf hfg hx

/-- **Stacks Project, Tag 05AR.** At a point whose local-ring maximal ideal is finitely
generated, associated and weakly associated membership of a sheaf of modules coincide. -/
@[stacks 05AR "finite_generated_maximal_ideal"]
theorem mem_associatedPoints_iff_mem_weaklyAssociatedPoints {X : Scheme.{u}} (F : X.Modules)
    (x : X) (h : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).FG) :
    x ∈ Stacks.Divisors.associatedPoints F ↔
      x ∈ Stacks.Divisors.weaklyAssociatedPoints F := by
  show IsAssociatedPrimeStacks _ (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) ↔
    IsWeaklyAssociatedPrime _ (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
      (IsLocalRing.maximalIdeal (X.presheaf.stalk x))
  unfold IsAssociatedPrimeStacks IsWeaklyAssociatedPrime
  simpa only [Submodule.colon_span, Submodule.bot_colon', eq_comm] using
    ((isAssociatedPrime_tfae_of_fg (R := X.presheaf.stalk x)
      (M := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) h).out 1 3)

/-- **Stacks Project, Tag 05AR.** On a locally Noetherian scheme, the associated points and
weakly associated points of a sheaf of modules coincide. -/
@[stacks 05AR "locally_noetherian"]
lemma associatedPoints_eq_weaklyAssociatedPoints (X : Scheme.{u}) [IsLocallyNoetherian X]
    (F : X.Modules) :
    Stacks.Divisors.associatedPoints F = Stacks.Divisors.weaklyAssociatedPoints F := by
  ext x
  exact mem_associatedPoints_iff_mem_weaklyAssociatedPoints F x
    (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).fg_of_isNoetherianRing

end AlgebraicGeometry
