module

public import Mathlib.RingTheory.Kaehler.TensorProduct
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
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
public import Mathlib.Topology.Sheaves.Init
public import StacksFrontier.RingTheory.Kaehler.JacobiZariski
import StacksCore.Tactic.StacksAttribute
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Kähler differentials under localization, base change and formally smooth towers

All rings are commutative with unit. This file records how the module of Kähler differentials
`Ω[S⁄R]` behaves under localization of the base ring and of the algebra, and under base change,
and shows that the sequence of differentials of a tower `R → A → B` with `A → B` formally smooth
is split short exact.

## Main results

* `omega_localization_base`: if `S ⊆ A` is a multiplicative subset whose image consists of
  units of `B`, so that `A → B` factors through `Aₛ = S⁻¹A`, then the canonical map
  `Ω_{B/A} → Ω_{B/Aₛ}` is an isomorphism of `B`-modules.
* `omega_localization_total`: if `S ⊆ B` is a multiplicative subset and `Bₛ = S⁻¹B`, then
  `Ω_{B/A} → Ω_{Bₛ/A}` exhibits `Ω_{Bₛ/A}` as `S⁻¹ Ω_{B/A}`.
* `KaehlerDifferential.exists_retraction_mapBaseChange`: for a tower `R → A → B` with `A → B`
  formally smooth, `KaehlerDifferential.mapBaseChange R A B : B ⊗[A] Ω[A⁄R] →ₗ[B] Ω[B⁄R]` admits a
  `B`-linear retraction, so that `0 → B ⊗_A Ω_{A/R} → Ω_{B/R} → Ω_{B/A} → 0` is split short exact.

## Implementation notes

In `omega_localization_base` the hypothesis that every element of `S` maps to a unit of `B` is
encoded by an `Aₛ`-algebra structure on `B` compatible with its `A`-algebra structure via
`IsScalarTower`. By the universal property of localization such a structure exists, uniquely,
exactly when each element of `S` maps to a unit of `B`.

Split short exactness is stated as the existence of a retraction of `mapBaseChange R A B`, which
is at once its injectivity and the splitting; exactness at `Ω[B⁄R]` is
`KaehlerDifferential.exact_mapBaseChange_map` and surjectivity of `Ω[B⁄R] → Ω[B⁄A]` is
`KaehlerDifferential.map_surjective`. Formal smoothness of `A → B` is equivalent to `Ω[B⁄A]`
being projective together with `H₁(L_{B⁄A}) = 0` (`Algebra.formallySmooth_iff`); the second gives
injectivity of `mapBaseChange R A B`, and the first splits the surjection.

## References

* [StacksProject 00RT](https://stacks.math.columbia.edu/tag/00RT)
* [StacksProject 00RV](https://stacks.math.columbia.edu/tag/00RV)
* [StacksProject 031K](https://stacks.math.columbia.edu/tag/031K)
-/

@[expose] public section

@[expose] public section

/-- Let `A → B` be a ring map and let `S ⊆ A` be a multiplicative subset whose image consists of
units of `B`, so that `B` is an `Aₛ = S⁻¹A`-algebra. Then the canonical `B`-linear map
`Ω_{B/A} → Ω_{B/Aₛ}` is bijective. -/
@[stacks 00RT "(1)", ega "0 20.5.5" "special case"]
theorem omega_localization_base
    (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
    (S : Submonoid A) (Aₛ : Type*) [CommRing Aₛ] [Algebra A Aₛ] [IsLocalization S Aₛ]
    [Algebra Aₛ B] [IsScalarTower A Aₛ B] :
    Function.Bijective (KaehlerDifferential.map A Aₛ B B) := by
  refine ⟨?_, KaehlerDifferential.map_surjective A Aₛ B⟩
  have : Algebra.FormallyUnramified A Aₛ :=
    Algebra.FormallyUnramified.of_isLocalization (M := S) (Rₘ := Aₛ)
  have : Subsingleton (Ω[Aₛ⁄A]) := (Algebra.formallyUnramified_iff A Aₛ).mp this
  have : Subsingleton (TensorProduct Aₛ B (Ω[Aₛ⁄A])) := by infer_instance
  have hexact := KaehlerDifferential.exact_mapBaseChange_map A Aₛ B
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, hy⟩ := (hexact x).mp hx
  rw [← hy, Subsingleton.elim y 0, map_zero]

/-- Let `A → B` be a ring map, let `S ⊆ B` be a multiplicative subset and `Bₛ = S⁻¹B`. Then the
canonical map `Ω_{B/A} → Ω_{Bₛ/A}` exhibits `Ω_{Bₛ/A}` as the localization `S⁻¹ Ω_{B/A}`. -/
@[stacks 00RT "(2)", ega "0 20.5.9"]
theorem omega_localization_total
    (A : Type*) [CommRing A] (B : Type*) [CommRing B] [Algebra A B]
    (S : Submonoid B) (Bₛ : Type*) [CommRing Bₛ] [Algebra B Bₛ] [IsLocalization S Bₛ]
    [Algebra A Bₛ] [IsScalarTower A B Bₛ] :
    IsLocalizedModule S (KaehlerDifferential.map A A B Bₛ) :=
  KaehlerDifferential.isLocalizedModule_map A B Bₛ S

/-!
## Base change of the module of differentials

For ring maps `R → R'` and `R → S` with `S' = S ⊗[R] R'`, the canonical map induces an
isomorphism `R' ⊗[R] Ω[S⁄R] ≅ Ω[S'⁄R']`; this is `KaehlerDifferential.tensorKaehlerEquivBase`, for
an arbitrary pushout square `Algebra.IsPushout R R' S S'`. The variant over `S'` itself,
`S' ⊗[S] Ω[S⁄R] ≅ Ω[S'⁄R']`, is `KaehlerDifferential.tensorKaehlerEquiv`.
-/

add_to_stacks 00RV "for an arbitrary pushout square, with the tensor factors in the other
  order" KaehlerDifferential.tensorKaehlerEquivBase
add_to_sga "3 III 0.12" "special case" KaehlerDifferential.tensorKaehlerEquivBase
add_to_sga "3 III 4.8" "(iii), special case" KaehlerDifferential.tensorKaehlerEquivBase
add_to_sga "3 VIA 1.3.2" "Differentials clause" KaehlerDifferential.tensorKaehlerEquivBase
add_to_sga "5 III 6.9" "special case" KaehlerDifferential.tensorKaehlerEquivBase
add_to_sga "7 VI 5.5" "special case" KaehlerDifferential.tensorKaehlerEquivBase
add_to_ega "0 21.3.6" "partial" KaehlerDifferential.tensorKaehlerEquivBase
add_to_ega "0 22.4.4.7" "more general" KaehlerDifferential.tensorKaehlerEquivBase
add_to_ega "0 22.4.8" "more general" KaehlerDifferential.tensorKaehlerEquivBase
add_to_ega "IV 16.4.5" "special case" KaehlerDifferential.tensorKaehlerEquivBase
add_to_ega "IV 16.5.10" "(16.5.10.1) affine case" KaehlerDifferential.tensorKaehlerEquivBase
add_to_stacks 00RV "the variant over the base-changed algebra"
  KaehlerDifferential.tensorKaehlerEquiv
add_to_ega "0 20.5.5" KaehlerDifferential.tensorKaehlerEquiv
add_to_ega "0 21.3.6" "partial" KaehlerDifferential.tensorKaehlerEquiv
add_to_ega "0 22.4.4.7" "more general" KaehlerDifferential.tensorKaehlerEquiv
add_to_ega "0 22.4.8" "more general" KaehlerDifferential.tensorKaehlerEquiv
add_to_ega "IV 16.5.10" "(16.5.10.1) affine case" KaehlerDifferential.tensorKaehlerEquiv
add_to_ega "0 20.5.5" KaehlerDifferential.tensorKaehlerEquivBase

open TensorProduct

attribute [local instance] Algebra.TensorProduct.rightAlgebra

@[expose] public section

open scoped TensorProduct

namespace Stacks.KaehlerDifferential.TowerSplitting

/-- **Splitting lemma with a projective quotient.** An exact sequence of modules
`M → N → P` with `f` injective, `g` surjective and `P` projective is left split: `f` admits a
retraction. -/
private theorem exists_retraction_of_exact_of_projective {R M N P : Type*} [Semiring R]
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N] [Module R P]
    [Module.Projective R P] {f : M →ₗ[R] N} {g : N →ₗ[R] P} (h : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g) :
    ∃ r : N →ₗ[R] M, r ∘ₗ f = LinearMap.id :=
  ((h.split_tfae hf hg).out 1 2).mp (Module.projective_lifting_property g LinearMap.id hg)

/-- For a tower `R → A → B` with `A → B` formally smooth, the canonical map
`B ⊗[A] Ω[A⁄R] → Ω[B⁄R]` admits a `B`-linear retraction. -/
public theorem solution (R : Type*) [CommRing R]
    (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Algebra.FormallySmooth A B] :
    ∃ r : Ω[B⁄R] →ₗ[B] B ⊗[A] Ω[A⁄R],
      r ∘ₗ KaehlerDifferential.mapBaseChange R A B = LinearMap.id :=
  have ⟨_, _⟩ := (Algebra.formallySmooth_iff A B).mp ‹_›
  exists_retraction_of_exact_of_projective (KaehlerDifferential.exact_mapBaseChange_map R A B)
    (_root_.KaehlerDifferential.mapBaseChange_injective R A B)
    (KaehlerDifferential.map_surjective R A B)

end Stacks.KaehlerDifferential.TowerSplitting

end

@[expose] public section

open scoped TensorProduct

/-- **The sequence of differentials of a tower is split short exact.** Let `R → A → B` be ring
maps with `A → B` formally smooth. Then the canonical injection `B ⊗_A Ω_{A/R} → Ω_{B/R}` admits
a `B`-linear retraction, so that `0 → B ⊗_A Ω_{A/R} → Ω_{B/R} → Ω_{B/A} → 0` is a split short
exact sequence. -/
@[stacks 031K "Split short exactness, i.e. the two assertions of the tag that are not already in
Mathlib (exactness at `Ω_{C/A}` is `KaehlerDifferential.exact_mapBaseChange_map` and surjectivity
is `KaehlerDifferential.map_surjective`), stated as the existence of a retraction of the
injection: that is at once its injectivity and the splitting. See the module docstring.",
  ega
  "0 20.5.7" "(ii), sufficiency",
  ega "IV 17.2.3" "(ii), affine case",
  ega "0 20.7.3" "discrete case, necessity",
  ega "0 20.7.2" "sufficiency",
  sga "1 II 4.3" "(i) inj., affine case",
  sga "1 II 4.4" "special case",
  sga "6 VIII 2.6" "partial"]
public theorem KaehlerDifferential.exists_retraction_mapBaseChange (R : Type*) [CommRing R]
    (A B : Type*) [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Algebra.FormallySmooth A B] :
    ∃ r : Ω[B⁄R] →ₗ[B] B ⊗[A] Ω[A⁄R],
      r ∘ₗ KaehlerDifferential.mapBaseChange R A B = LinearMap.id :=
  Stacks.KaehlerDifferential.TowerSplitting.solution R A B

end
