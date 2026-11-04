module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.FiniteTypeOpenLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.PointwiseOpenLocus
public import StacksFrontier.RingTheory.Flat.FlatLocusFiniteTypeAlgebra

/-!
# The flat locus of a morphism locally of finite type

For a morphism of schemes `f : X ⟶ S` locally of finite presentation the set of points at which
`f` is flat is open with no hypothesis on the base; that is Stacks 0399. For a morphism only
locally of finite type openness becomes a condition on the base, and it holds when the weakly
associated points of `S` are locally finite. On the resulting open subscheme `f` is flat, and
over an integral base it is moreover locally of finite presentation.

## Main results

* `AlgebraicGeometry.isOpen_setOf_isFlatAt_of_locallyOfFiniteType_of_locally_finite_weakAss` is
  the openness assertion of Stacks 05IM, and
  `AlgebraicGeometry.locallyOfFinitePresentation_restrict_of_subset_flatLocus` its
  finite-presentation assertion.
* `AlgebraicGeometry.locallyOfFinitePresentation_of_flat_of_isIntegral` is Stacks 05IN.

Flatness on the flat locus, the remaining assertion of Stacks 05IM, needs no hypothesis and is
`AlgebraicGeometry.flat_of_subset_setOf_isFlatAt`.

## References

* [Stacks Project, Tag 05IM](https://stacks.math.columbia.edu/tag/05IM)
* [Stacks Project, Tag 05IN](https://stacks.math.columbia.edu/tag/05IN)
-/

@[expose] public section

open CategoryTheory Stacks.Divisors

universe u

namespace AlgebraicGeometry

/-- **Openness of the flat locus.** For a morphism `f : X ⟶ S` locally of finite type whose base
has locally finite weakly associated points, the set of points at which `f` is flat is open. -/
@[stacks 05IM "openness of the locus of flatness"]
theorem isOpen_setOf_isFlatAt_of_locallyOfFiniteType_of_locally_finite_weakAss
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (hS : ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
      (schemeWeaklyAssociatedPoints S ∩ (V : Set S)).Finite) :
    IsOpen {x : X | IsFlatAt f.toLRSHom.toShHom x} :=
  isOpen_setOf_isFlatAt_of_locallyOfFiniteType f hS fun _ _ _ _ _ _ hA =>
    Stacks.Flatness.isOpen_setOf_flat_localizedModule_atPrime_of_finiteType hA

/-- A morphism locally of finite type and flat over an integral base is locally of finite
presentation. -/
@[stacks 05IN]
theorem locallyOfFinitePresentation_of_flat_of_isIntegral
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [Flat f] [IsIntegral S] :
    LocallyOfFinitePresentation f := by
  refine ⟨fun {U} hU {V} hV e => ?_⟩
  let : Algebra Γ(S, U) Γ(X, V) := (f.appLE U V e).hom.toAlgebra
  have hft : Algebra.FiniteType Γ(S, U) Γ(X, V) := f.finiteType_appLE hU hV e
  have hflat : Module.Flat Γ(S, U) Γ(X, V) := f.flat_appLE hU hV e
  rcases isEmpty_or_nonempty U with hempty | hne
  · have hUbot : U = ⊥ := TopologicalSpace.Opens.ext (Set.isEmpty_coe_sort.mp hempty)
    have hsubA : Subsingleton Γ(S, U) := hUbot ▸ inferInstance
    have hsubB : Subsingleton Γ(X, V) :=
      subsingleton_of_zero_eq_one
        (by rw [← map_one (f.appLE U V e).hom, Subsingleton.elim (1 : Γ(S, U)) 0, map_zero])
    have hsurj : Function.Surjective (algebraMap Γ(S, U) Γ(X, V)) :=
      fun b => ⟨0, Subsingleton.elim _ _⟩
    refine Algebra.FinitePresentation.of_surjective (f := Algebra.ofId Γ(S, U) Γ(X, V))
      hsurj ⟨{1}, ?_⟩
    rw [Finset.coe_singleton, Ideal.span_singleton_one]
    exact (eq_top_iff.mpr fun x _ => Subsingleton.elim _ _).symm
  · have : IsDomain Γ(S, U) := IsIntegral.component_integral U
    exact Stacks.Flatness.finitePresentation_of_flat_of_finiteType_of_isDomain

/-- **A flat morphism locally of finite type over a base with locally finite weakly associated
points is locally of finite presentation.** This is the finite-presentation assertion of
Stacks 05IM, in the form that does not refer to the flat locus. -/
theorem locallyOfFinitePresentation_of_flat_of_locally_finite_weakAss
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] [Flat f]
    (hS : ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
      (schemeWeaklyAssociatedPoints S ∩ (V : Set S)).Finite) :
    LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_exists_appLE (P := @LocallyOfFinitePresentation)
    (RingHom.finitePresentation_stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.finitePresentation_holdsForLocalizationAway).1]
  intro x
  obtain ⟨W₀, hxW₀, hW₀fin⟩ := hS (f x)
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWW₀⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open hxW₀ W₀.2
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxW (f ⁻¹ᵁ W).2
  refine ⟨⟨W, hW⟩, ⟨V, hV⟩, hxV, hVW, ?_⟩
  let _ : Algebra Γ(S, W) Γ(X, V) := (f.appLE W V hVW).hom.toAlgebra
  have : Algebra.FiniteType Γ(S, W) Γ(X, V) := f.finiteType_appLE hW hV hVW
  have : Module.Flat Γ(S, W) Γ(X, V) := f.flat_appLE hW hV hVW
  exact RingHom.finitePresentation_algebraMap.mp
    (Stacks.Flatness.finitePresentation_of_flat_of_finiteType
      (weaklyAssociatedPrimes_sections_finite (SheafOfModules.unit S.ringCatSheaf) hW hWW₀ hW₀fin))

/-- **Finite presentation on the flat locus.** For a morphism `f : X ⟶ S` locally of finite type
whose base has locally finite weakly associated points, the restriction of `f` to an open
subscheme contained in the locus of points of flatness is locally of finite presentation. -/
@[stacks 05IM "the flat locus is locally of finite presentation over the base"]
theorem locallyOfFinitePresentation_restrict_of_subset_flatLocus
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (hS : ∀ s : S, ∃ V : S.Opens, s ∈ V ∧
      (schemeWeaklyAssociatedPoints S ∩ (V : Set S)).Finite)
    (U : X.Opens) (hU : (U : Set X) ⊆ {x : X | IsFlatAt f.toLRSHom.toShHom x}) :
    LocallyOfFinitePresentation (U.ι ≫ f) :=
  have : Flat (U.ι ≫ f) := flat_of_subset_setOf_isFlatAt f U hU
  locallyOfFinitePresentation_of_flat_of_locally_finite_weakAss (U.ι ≫ f) hS

end AlgebraicGeometry
