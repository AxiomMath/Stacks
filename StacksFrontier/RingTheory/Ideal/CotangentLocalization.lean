module
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
public import Mathlib.RingTheory.WittVector.IsPoly
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

/-!
# Localization commutes with the conormal module

Let `R` be a commutative ring, let `M ⊆ R` be a submonoid, let `A` be a localization of `R` at
`M` and let `I ⊆ R` be an ideal. Writing `I_A = I·A` for the extended ideal, the natural map
`I/I² → I_A/I_A²` exhibits `I_A/I_A²` as the localization of `I/I²` at `M`. In other words the
formation of the conormal module of an ideal commutes with localization, because localization is
exact.

The case `M = 𝔮'.primeCompl` for a prime `𝔮' ⊆ R` is the identification the criteria of Stacks
00SC are stated with: the conormal module `(I/I²)_𝔮` of a presentation `S = k[x_i]/I` at a prime
`𝔮 ⊆ S` and the conormal module of the ideal `I_{𝔮'}` of `k[x_i]_{𝔮'}` are the same module.

## Main results

* `Ideal.localizedCotangentMap`: the natural map `I/I² → I_A/I_A²`.
* `Ideal.isLocalizedModule_localizedCotangentMap`: it is a localization at `M`.
* `Ideal.localizedCotangentEquiv`: consequently *any* localization of `I/I²` at `M` is
  `R`-linearly isomorphic to `I_A/I_A²`.

## Implementation notes

The `Away` case of `Ideal.isLocalizedModule_localizedCotangentMap`, for the submonoid
`Submonoid.powers g` and with the extended ideal presented by a finite list of generators, is
`Quasiregular.cotangentMapAway_isLocalizedModule` in
`StacksFrontier.RingTheory.Regular.Quasiregular`; the proof here is that
proof with `Submonoid.powers g` replaced by an arbitrary submonoid, which costs nothing —
`IsLocalization.map_units`, `IsLocalization.mem_map_algebraMap_iff` and
`IsLocalization.eq_iff_exists` are all available for a general submonoid.
-/

@[expose] public section

universe u v

namespace Ideal

variable {R : Type u} [CommRing R]

/-- The natural map `I/I² → I_A/I_A²` induced by a localization `A` of `R`, where
`I_A = I·A`. -/
noncomputable def localizedCotangentMap (M : Submonoid R) (A : Type v) [CommRing A] [Algebra R A]
    [IsLocalization M A] (I : Ideal R) :
    I.Cotangent →ₗ[R] (I.map (algebraMap R A)).Cotangent :=
  I.mapCotangent (I.map (algebraMap R A)) (Algebra.ofId R A)
    (show I ≤ Ideal.comap (Algebra.ofId R A) (I.map (algebraMap R A)) from
      fun _ hx => Ideal.mem_map_of_mem (algebraMap R A) hx)

/-- `localizedCotangentMap` sends the class of `a ∈ I` in `I/I²` to the class
in `I_A/I_A²` of its image in `I_A`. -/
theorem localizedCotangentMap_toCotangent (M : Submonoid R) (A : Type v) [CommRing A]
    [Algebra R A] [IsLocalization M A] (I : Ideal R) (a : R) (ha : a ∈ I) :
    localizedCotangentMap M A I (I.toCotangent ⟨a, ha⟩)
      = (I.map (algebraMap R A)).toCotangent
          ⟨algebraMap R A a, Ideal.mem_map_of_mem _ ha⟩ := by
  rw [localizedCotangentMap, Ideal.mapCotangent_toCotangent]
  rfl

/-- **Localization commutes with the conormal module.** For a localization `A` of `R` at a
submonoid `M` and an ideal `I ⊆ R`, the natural map `I/I² → I_A/I_A²` exhibits the conormal
module of the extended ideal `I_A = I·A` as the localization of `I/I²` at `M`.

This is exactness of localization: `I_A/I_A²` is `(I/I²) ⊗_R A`. -/
theorem isLocalizedModule_localizedCotangentMap (M : Submonoid R) (A : Type v) [CommRing A]
    [Algebra R A] [IsLocalization M A] (I : Ideal R) :
    IsLocalizedModule M (localizedCotangentMap M A I) := by
  have smulJ : ∀ (s : R) (w : A) (hw : w ∈ I.map (algebraMap R A)),
      s • ((I.map (algebraMap R A)).toCotangent ⟨w, hw⟩)
        = (I.map (algebraMap R A)).toCotangent
            ⟨algebraMap R A s * w, Ideal.mul_mem_left _ _ hw⟩ := by
    intro s w hw
    rw [← IsScalarTower.algebraMap_smul A, ← LinearMap.map_smul]
    congr 1
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · -- multiplication by `s ∈ M` is bijective on the target
    intro s
    obtain ⟨u, hu⟩ : IsUnit (algebraMap R A (s : R)) := IsLocalization.map_units A s
    rw [Module.End.isUnit_iff]
    have h : ⇑(algebraMap R (Module.End R (I.map (algebraMap R A)).Cotangent) (s : R)) =
        (u • ·) := by
      ext m
      rw [Module.algebraMap_end_apply, ← IsScalarTower.algebraMap_smul A, ← hu]
      rfl
    rw [h]
    exact MulAction.bijective u
  · -- every element of the target is `θ m / s`
    intro y
    obtain ⟨⟨w, hw⟩, rfl⟩ := (I.map (algebraMap R A)).toCotangent_surjective y
    rw [IsLocalization.mem_map_algebraMap_iff M A] at hw
    obtain ⟨⟨⟨a, ha⟩, ⟨s, hs⟩⟩, heq⟩ := hw
    simp only at heq
    refine ⟨⟨I.toCotangent ⟨a, ha⟩, ⟨s, hs⟩⟩, ?_⟩
    show s • ((I.map (algebraMap R A)).toCotangent ⟨_, _⟩) = _
    rw [smulJ, localizedCotangentMap_toCotangent]
    congr 1
    apply Subtype.ext
    show algebraMap R A s * _ = algebraMap R A a
    rw [mul_comm]
    exact heq
  · -- the kernel condition
    intro x₁ x₂ hx
    have hm : (localizedCotangentMap M A I) (x₁ - x₂) = 0 := by rw [map_sub, hx, sub_self]
    obtain ⟨⟨a, ha⟩, hrep⟩ := I.toCotangent_surjective (x₁ - x₂)
    rw [← hrep, localizedCotangentMap_toCotangent] at hm
    have hker : (⟨algebraMap R A a, Ideal.mem_map_of_mem _ ha⟩ : ↥(I.map (algebraMap R A)))
        ∈ (I.map (algebraMap R A)).toCotangent.ker := hm
    rw [Ideal.mem_toCotangent_ker] at hker
    have hmem : algebraMap R A a ∈ (I.map (algebraMap R A)) ^ 2 := hker
    rw [← Ideal.map_pow, IsLocalization.mem_map_algebraMap_iff M A] at hmem
    obtain ⟨⟨⟨b, hb⟩, ⟨s, hs⟩⟩, heq⟩ := hmem
    simp only [← map_mul] at heq
    rw [IsLocalization.eq_iff_exists M A] at heq
    obtain ⟨⟨c, hc⟩, hceq⟩ := heq
    refine ⟨⟨c * s, mul_mem hc hs⟩, ?_⟩
    have hz : ((c * s : R)) • (x₁ - x₂) = 0 := by
      rw [← hrep, ← LinearMap.map_smul, ← LinearMap.mem_ker, Ideal.mem_toCotangent_ker]
      show (c * s) * a ∈ I ^ 2
      rw [show (c * s) * a = c * (a * s) by ring, hceq]
      exact Ideal.mul_mem_left _ _ hb
    rw [smul_sub, sub_eq_zero] at hz
    exact hz

/-- **Any localization of `I/I²` at `M` is the conormal module of the extended ideal.** This is
`Ideal.isLocalizedModule_localizedCotangentMap` together with the uniqueness of localized
modules. -/
noncomputable def localizedCotangentEquiv (M : Submonoid R) (A : Type v) [CommRing A]
    [Algebra R A] [IsLocalization M A] (I : Ideal R) (N : Type*) [AddCommGroup N] [Module R N]
    (F : I.Cotangent →ₗ[R] N) [IsLocalizedModule M F] :
    N ≃ₗ[R] (I.map (algebraMap R A)).Cotangent :=
  haveI := isLocalizedModule_localizedCotangentMap M A I
  IsLocalizedModule.linearEquiv M F (localizedCotangentMap M A I)


end Ideal

end
