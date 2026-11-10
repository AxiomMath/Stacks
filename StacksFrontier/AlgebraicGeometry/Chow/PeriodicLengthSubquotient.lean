module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import StacksCore.Algebra.Homology.HomologicalComplexAbelian
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Additivity

/-!
# The multiplicity of a two-periodic complex along a stable submodule

A submodule carried into itself by both differentials of a two-periodic complex gives two further
two-periodic complexes, on the submodule and on the quotient, and the multiplicity of the
original is the sum of theirs. The inclusion and the quotient map form a short exact sequence of
two-periodic complexes, so this is again additivity of the multiplicity on a short exact
sequence.

## Main results

* `AlgebraicGeometry.periodicLength_eq_of_iso`: isomorphic two-periodic complexes have the same
  multiplicity.
* `AlgebraicGeometry.restrict_mul_restrict_eq_zero` and
  `AlgebraicGeometry.mapQ_mul_mapQ_eq_zero`: the restricted and the induced differentials again
  annihilate each other.
* `AlgebraicGeometry.periodicLength_add_of_stable`: the multiplicity of the complex is the sum of
  the multiplicities on the stable submodule and on its quotient.
* `AlgebraicGeometry.hasFiniteLengthHomology_restrict_of_stable`: finite-length cohomology
  passes to the stable submodule, by two-out-of-three.

## Implementation notes

The two morphisms of complexes are built with `AlgebraicGeometry.twoPeriodicComplexMap` from
`Submodule.subtype` and `Submodule.mkQ`, which intertwine the differentials by construction of
`LinearMap.restrict` and `Submodule.mapQ`. Short exactness is checked degree by degree, using
`LinearMap.exact_subtype_mkQ`.

`AlgebraicGeometry.periodicLength_eq_of_iso` duplicates a lemma of the same statement which is
`private` in `StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Comparison`. The
duplication is deliberate: a `private` declaration is module-local, so that one is invisible
outside its own module and cannot be used here, and widening its interface is not this module's
business. The proof follows the public analogue in the parallel `Stacks.Chow` development.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable {R : Type u} [Ring R] {M : Type v} [AddCommGroup M] [Module R M]

/-- Isomorphic two-periodic complexes have the same multiplicity. -/
theorem periodicLength_eq_of_iso
    {K L : HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2))} (e : K ≅ L) :
    periodicLength K = periodicLength L := by
  have h (i : ZMod 2) : Module.length R (K.homology i) = Module.length R (L.homology i) :=
    ((HomologicalComplex.homologyFunctor (ModuleCat.{v} R)
      (ComplexShape.up (ZMod 2)) i).mapIso e).toLinearEquiv.length_eq
  simp only [periodicLength, h]

/-- Endomorphisms annihilating each other still do so after restriction to a stable
submodule. -/
theorem restrict_mul_restrict_eq_zero (φ ψ : Module.End R M) (h : φ * ψ = 0)
    {K : Submodule R M} (hφ : ∀ x ∈ K, φ x ∈ K) (hψ : ∀ x ∈ K, ψ x ∈ K) :
    φ.restrict hφ * ψ.restrict hψ = 0 := by
  refine LinearMap.ext fun x ↦ Subtype.ext ?_
  simpa [LinearMap.restrict_apply] using LinearMap.congr_fun h (x : M)

/-- Endomorphisms annihilating each other still do so on the quotient by a stable submodule. -/
theorem mapQ_mul_mapQ_eq_zero (φ ψ : Module.End R M) (h : φ * ψ = 0)
    {K : Submodule R M} (hφ : ∀ x ∈ K, φ x ∈ K) (hψ : ∀ x ∈ K, ψ x ∈ K) :
    K.mapQ K φ hφ * K.mapQ K ψ hψ = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | H m => simpa using congrArg K.mkQ (LinearMap.congr_fun h m)

/-- The multiplicity of a two-periodic complex is the multiplicity on a stable submodule plus
the multiplicity on the quotient by it. -/
theorem periodicLength_add_of_stable (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    {K : Submodule R M} (hφK : ∀ x ∈ K, φ x ∈ K) (hψK : ∀ x ∈ K, ψ x ∈ K)
    (hsubφψ : φ.restrict hφK * ψ.restrict hψK = 0)
    (hsubψφ : ψ.restrict hψK * φ.restrict hφK = 0)
    (hquotφψ : K.mapQ K φ hφK * K.mapQ K ψ hψK = 0)
    (hquotψφ : K.mapQ K ψ hψK * K.mapQ K φ hφK = 0)
    (hfinK : HasFiniteLengthHomology
      (twoPeriodicComplex (φ.restrict hφK) (ψ.restrict hψK) hsubφψ hsubψφ))
    (hfinQ : HasFiniteLengthHomology
      (twoPeriodicComplex (K.mapQ K φ hφK) (K.mapQ K ψ hψK) hquotφψ hquotψφ)) :
    periodicLength (twoPeriodicComplex φ ψ hφψ hψφ) =
      periodicLength (twoPeriodicComplex (φ.restrict hφK) (ψ.restrict hψK) hsubφψ hsubψφ) +
        periodicLength
          (twoPeriodicComplex (K.mapQ K φ hφK) (K.mapQ K ψ hψK) hquotφψ hquotψφ) := by
  let S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2))) :=
    { f := twoPeriodicComplexMap (φ.restrict hφK) (ψ.restrict hψK) hsubφψ hsubψφ φ ψ hφψ hψφ
        K.subtype (LinearMap.subtype_comp_restrict hφK) (LinearMap.subtype_comp_restrict hψK)
      g := twoPeriodicComplexMap φ ψ hφψ hψφ (K.mapQ K φ hφK) (K.mapQ K ψ hψK) hquotφψ hquotψφ
        K.mkQ (LinearMap.ext fun m ↦ by simp) (LinearMap.ext fun m ↦ by simp)
      zero := by
        ext i x
        change K.mkQ (K.subtype x) = 0
        simpa using x.2 }
  refine periodicLength_additive_of_shortExact S (.mk' ?_ ?_ ?_) (Or.inr (Or.inl ⟨hfinK, hfinQ⟩))
  · rw [HomologicalComplex.exact_iff_degreewise_exact]
    intro i
    refine (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr ?_
    change Function.Exact K.subtype K.mkQ
    exact LinearMap.exact_subtype_mkQ K
  · rw [HomologicalComplex.mono_iff_degreewise_mono]
    intro i
    change Mono (ModuleCat.ofHom K.subtype)
    exact ConcreteCategory.mono_of_injective _ K.injective_subtype
  · rw [HomologicalComplex.epi_iff_degreewise_epi]
    intro i
    change Epi (ModuleCat.ofHom K.mkQ)
    exact ConcreteCategory.epi_of_surjective _ K.mkQ_surjective

/-- Finite-length cohomology passes to a stable submodule, given it for the module and for the
quotient: the three complexes form a short exact sequence, so this is two-out-of-three. -/
theorem hasFiniteLengthHomology_restrict_of_stable
    (φ ψ : Module.End R M) (hφψ : φ * ψ = 0) (hψφ : ψ * φ = 0)
    {K : Submodule R M} (hφK : ∀ x ∈ K, φ x ∈ K) (hψK : ∀ x ∈ K, ψ x ∈ K)
    (hsubφψ : φ.restrict hφK * ψ.restrict hψK = 0)
    (hsubψφ : ψ.restrict hψK * φ.restrict hφK = 0)
    (hquotφψ : K.mapQ K φ hφK * K.mapQ K ψ hψK = 0)
    (hquotψφ : K.mapQ K ψ hψK * K.mapQ K φ hφK = 0)
    (hfinM : HasFiniteLengthHomology (twoPeriodicComplex φ ψ hφψ hψφ))
    (hfinQ : HasFiniteLengthHomology
      (twoPeriodicComplex (K.mapQ K φ hφK) (K.mapQ K ψ hψK) hquotφψ hquotψφ)) :
    HasFiniteLengthHomology
      (twoPeriodicComplex (φ.restrict hφK) (ψ.restrict hψK) hsubφψ hsubψφ) := by
  let S : ShortComplex (HomologicalComplex (ModuleCat.{v} R) (ComplexShape.up (ZMod 2))) :=
    { f := twoPeriodicComplexMap (φ.restrict hφK) (ψ.restrict hψK) hsubφψ hsubψφ φ ψ hφψ hψφ
        K.subtype (LinearMap.subtype_comp_restrict hφK) (LinearMap.subtype_comp_restrict hψK)
      g := twoPeriodicComplexMap φ ψ hφψ hψφ (K.mapQ K φ hφK) (K.mapQ K ψ hψK) hquotφψ hquotψφ
        K.mkQ (LinearMap.ext fun m ↦ by simp) (LinearMap.ext fun m ↦ by simp)
      zero := by
        ext i x
        change K.mkQ (K.subtype x) = 0
        simpa using x.2 }
  refine finiteLengthHomology_X1_of_shortExact S (.mk' ?_ ?_ ?_) hfinM hfinQ
  · rw [HomologicalComplex.exact_iff_degreewise_exact]
    intro i
    refine (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mpr ?_
    change Function.Exact K.subtype K.mkQ
    exact LinearMap.exact_subtype_mkQ K
  · rw [HomologicalComplex.mono_iff_degreewise_mono]
    intro i
    change Mono (ModuleCat.ofHom K.subtype)
    exact ConcreteCategory.mono_of_injective _ K.injective_subtype
  · rw [HomologicalComplex.epi_iff_degreewise_epi]
    intro i
    change Epi (ModuleCat.ofHom K.mkQ)
    exact ConcreteCategory.epi_of_surjective _ K.mkQ_surjective

end AlgebraicGeometry

end
