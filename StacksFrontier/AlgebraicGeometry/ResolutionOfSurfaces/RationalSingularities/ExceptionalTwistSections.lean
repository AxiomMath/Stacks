module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerCohomologySequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalTwistCohomology
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalIdealPowersExtra

/-!
# The global sections of the nonnegative twists on the exceptional curve

In Situation [Stacks, Tag 0B4W] let `X` be the blowup of `Spec(A)` in the maximal ideal, let
`i : E ⟶ X` be its exceptional divisor and let `𝒪_E(n)` be the `n`-th twist on `E`. This file
proves clause (5) of [Stacks, Tag 0B63]: `H⁰(E, 𝒪_E(n)) = 𝔪ⁿ/𝔪ⁿ⁺¹` for every `n ≥ 0`.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.nonempty_curveTwistSheafSections_iso_gradedPiece`:
  **clause (5) of [Stacks, Tag 0B63]**.
* `AlgebraicGeometry.BlowUpDualizing`
  `.surjective_moduleGlobalSections_map_exceptionalTwistedSequence_g` and
  `.range_eq_ker_moduleGlobalSections_map_exceptionalTwistedSequence`: the restriction
  sequence on global sections is exact and surjective on the right.
* `AlgebraicGeometry.BlowUpDualizing`
  `.mem_range_moduleGlobalSections_map_exceptionalTwistedSequence_f`: the first map of the
  restriction sequence is, on global sections, the inclusion `𝔪ⁿ⁺¹ ⊆ 𝔪ⁿ`.
* `AlgebraicGeometry.BlowUpDualizing.exceptionalIdealPowSectionsEquivIdeal`: `H⁰(X, ℐⁿ) = 𝔪ⁿ`,
  the global-sections conclusion of [Stacks, Tag 0B4Y], as an isomorphism of
  `Γ(X, 𝒪_X)`-modules.

## The argument

Clause (5) is read off the restriction sequence
`0 ⟶ ℐⁿ⁺¹ ⟶ ℐⁿ ⟶ i_*𝒪_E(n) ⟶ 0`
(`AlgebraicGeometry.BlowUpDualizing.exceptionalTwistedSequence`) in degree zero:

* `H¹(X, ℐⁿ⁺¹) = 0` — [Stacks, Tag 0B4Y] — makes `H⁰(X, ℐⁿ) ⟶ H⁰(X, i_*𝒪_E(n))` surjective
  (`Stacks.Cohomology.SectionsEpi.epi_moduleGlobalSections_map_of_isZero_rightDerived_one`);
* the kernel of that map is the image of `H⁰(X, ℐⁿ⁺¹)`, by the long exact sequence of the
  cohomological `δ`-functor of [Stacks, Tag 010Q] in degree zero, with
  `CategoryTheory.Functor.rightDerivedZeroIsoSelf` identifying `R⁰Γ` with `Γ`;
* that image is `𝔪ⁿ⁺¹`, because the first map of the sequence is the inclusion of ideal sheaves
  and the global sections of `ℐᵐ` are `𝔪ᵐ` — again [Stacks, Tag 0B4Y].

**No `H²` is used**, so none of the eventual vanishing of [Stacks, Tag 02O1] enters; clause (5)
rests on [Stacks, Tag 0B4Y] alone.

## Implementation notes

**Two readings of the category of `𝒪_X`-modules.** The inclusion `ℐ ⟶ 𝒪_X` of a sheaf of ideals
is stated over `structureSheafRing X.toRingedSpace`, the restriction sequence over
`X.Modules`; the two are the same category, but only at default transparency, so an equation
between composites written across the boundary is not one `rw` or `simp` can traverse.
`AlgebraicGeometry.BlowUpDualizing.exceptionalIdealPowSections` crosses the boundary once, by
applying global sections: after that everything lives in the unambiguous `ModuleCat Γ(X, 𝒪_X)`,
and `exceptionalIdealPowSections_square` is proved from the morphism equation by `Functor.map_comp`
applied as a term rather than rewritten with.

**The `A`-module structure.** The statement of clause (5) reads the global sections on `E` as an
`A`-module by restricting scalars along `A ≅ Γ(X, 𝒪_X) ⟶ Γ(E, 𝒪_E)`;
`ModuleCat.restrictScalarsComp'App` splits that into its two steps and
`Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop` — [Stacks, Tag 01EZ] over the whole
space — is the second one. Everything cohomological is done over `Γ(X, 𝒪_X)` and carried to `A`
by the functor `ModuleCat.restrictScalars`, so no element of a restricted module is ever fed to a
`Γ(X, 𝒪_X)`-linear map; the passage from `ψ(𝔪ⁿ)/ψ(𝔪ⁿ⁺¹)` to `𝔪ⁿ/𝔪ⁿ⁺¹` is the self-contained
`gradedPieceEquiv`, which is commutative algebra about a bijective ring homomorphism.

## References

* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B4Y](https://stacks.math.columbia.edu/tag/0B4Y)
* [Stacks Project, Tag 010Q](https://stacks.math.columbia.edu/tag/010Q)
* [Stacks Project, Tag 01EZ](https://stacks.math.columbia.edu/tag/01EZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor)
open Stacks.Divisors (idealSheafOfModules)

attribute [local instance 2000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.BlowUpDualizing

/-! ### Two algebraic lemmas -/

/-- For a bijective ring homomorphism, membership in the image ideal detects membership. -/
private theorem mem_map_iff_of_bijective {A R : Type u} [CommRing A] [CommRing R]
    (f : A →+* R) (hf : Function.Bijective f) (J : Ideal A) (a : A) :
    f a ∈ Ideal.map f J ↔ a ∈ J := by
  have h := Ideal.comap_map_of_surjective f hf.2 J
  have hker : RingHom.ker f = ⊥ := (RingHom.injective_iff_ker_eq_bot f).1 hf.1
  rw [← RingHom.ker_eq_comap_bot, hker, sup_bot_eq] at h
  refine ⟨fun ha => ?_, Ideal.mem_map_of_mem f⟩
  have hmem : a ∈ Ideal.comap f (Ideal.map f J) := ha
  rwa [h] at hmem

/-- **`𝔪·𝔪ⁿ` inside `𝔪ⁿ` is `𝔪ⁿ⁺¹`.** An element of `𝔪ⁿ` lies in the submodule `𝔪 · 𝔪ⁿ` exactly
when it lies in `𝔪ⁿ⁺¹`; this is what makes the quotient `𝔪ⁿ/(𝔪·𝔪ⁿ)` — the shape
`Ideal.Cotangent` is written in, and the shape of the source's `𝔪ⁿ/𝔪ⁿ⁺¹` — a quotient by
`𝔪ⁿ⁺¹`. -/
private theorem mem_smul_top_iff {A : Type u} [CommRing A] (J : Ideal A) (n : ℕ)
    (x : (J ^ n : Ideal A)) :
    x ∈ (J • ⊤ : Submodule A (J ^ n : Ideal A)) ↔ (x : A) ∈ J ^ (n + 1) := by
  have hmap : Submodule.map (J ^ n : Ideal A).subtype (J • ⊤) = J ^ (n + 1) := by
    rw [Submodule.map_smul'', Submodule.map_subtype_top, pow_succ', Ideal.smul_eq_mul]
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · rw [← hmap]
    exact Submodule.mem_map_of_mem hx
  · rw [← hmap] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := Subtype.ext hyx
    exact this ▸ hy

variable (S : RationalSingularitySituation.{u})

/-! ### Global sections of the inclusion of a sheaf of ideals -/

/-- **The inclusion `H⁰(X, ℐⁿ) ⟶ Γ(X, 𝒪_X)`** induced by the inclusion `ℐⁿ ⟶ 𝒪_X` of the `n`-th
power of the ideal sheaf of the exceptional divisor.

Its source is the middle term of the restriction sequence on the nose. Naming it is what keeps
every statement below inside the unambiguous category `ModuleCat Γ(X, 𝒪_X)`: the inclusion of a
sheaf of ideals is stated over the `structureSheafRing` spelling of the sheaf of rings, which is
the same category as `X.Modules` only at default transparency, so an equation between composites
written with it is not one `rw` or `simp` can traverse. -/
def exceptionalIdealPowSections (n : ℕ) :
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
        (exceptionalTwistedSequence S.A n).X₂ ⟶
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
        (unitModule (blowUpScheme S.A)) :=
  (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
    (Stacks.Divisors.idealInclusion (exceptionalIdeal (centre S.A) ^ n))

/-- **The inclusion `H⁰(X, ℐ·ℐⁿ) ⟶ Γ(X, 𝒪_X)`**, the companion of `exceptionalIdealPowSections`
at the first term of the restriction sequence. -/
def exceptionalIdealMulPowSections (n : ℕ) :
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
        (idealSheafOfModules (exceptionalIdeal (centre S.A) *
          exceptionalIdeal (centre S.A) ^ n)) ⟶
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
        (unitModule (blowUpScheme S.A)) :=
  (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
    (Stacks.Divisors.idealInclusion
      (exceptionalIdeal (centre S.A) * exceptionalIdeal (centre S.A) ^ n))

/-- **`H⁰(X, ℐⁿ) ⟶ Γ(X, 𝒪_X)` is injective**, the ideal sheaf being a subsheaf of the structure
sheaf. -/
theorem injective_exceptionalIdealPowSections (n : ℕ) :
    Function.Injective (exceptionalIdealPowSections S n).hom :=
  Stacks.Divisors.idealSheafSection_injective (exceptionalIdeal (centre S.A) ^ n)

/-- **The range of `H⁰(X, ℐⁿ) ⟶ Γ(X, 𝒪_X)` is `H⁰(X, ℐⁿ)` read as an ideal of `Γ(X, 𝒪_X)`.** -/
theorem mem_range_exceptionalIdealPowSections (n : ℕ) (a : Γ(blowUpScheme S.A, ⊤)) :
    a ∈ LinearMap.range (exceptionalIdealPowSections S n).hom ↔
      a ∈ idealSheafGlobalSections (exceptionalIdeal (centre S.A) ^ n) :=
  Iff.symm (mem_idealSheafGlobalSections_iff (exceptionalIdeal (centre S.A) ^ n) a)

/-- The same for the first term of the sequence. -/
theorem mem_range_exceptionalIdealMulPowSections (n : ℕ) (a : Γ(blowUpScheme S.A, ⊤)) :
    a ∈ LinearMap.range (exceptionalIdealMulPowSections S n).hom ↔
      a ∈ idealSheafGlobalSections
        (exceptionalIdeal (centre S.A) * exceptionalIdeal (centre S.A) ^ n) :=
  Iff.symm (mem_idealSheafGlobalSections_iff
    (exceptionalIdeal (centre S.A) * exceptionalIdeal (centre S.A) ^ n) a)

/-! ### The identification `A ≅ Γ(X, 𝒪_X)` -/

/-- `ψ : A ⟶ Γ(X, 𝒪_X)`, the identification of [Stacks, Tag 0B4Y] at the blowup of the maximal
ideal, as a ring homomorphism. -/
def globalFunctionsRingHom : S.A →+* Γ(blowUpScheme S.A, ⊤) :=
  ((Scheme.ΓSpecIso (.of S.A)).inv ≫ (blowUpToBase (centre S.A)).appTop).hom

/-- **`ψ` is bijective**, which is the conclusion `Γ(X, 𝒪_X) = A` of [Stacks, Tag 0B4Y]. -/
theorem bijective_globalFunctionsRingHom : Function.Bijective (globalFunctionsRingHom S) :=
  have := isIso_globalFunctions_blowUpToBase_residuePoint S
  ConcreteCategory.bijective_of_isIso _

/-- **[Stacks, Tag 0B4Y]: `H⁰(X, ℐⁿ) = 𝔪ⁿ`**, at the spelling of the ideal sheaf used here. -/
theorem idealSheafGlobalSections_exceptionalIdealPow_centre (n : ℕ) :
    idealSheafGlobalSections (exceptionalIdeal (centre S.A) ^ n) =
      Ideal.map (globalFunctionsRingHom S) (IsLocalRing.maximalIdeal S.A ^ n) := by
  have hid : (rationalSingularitySituationBlowUp S).exceptionalIdeal =
      exceptionalIdeal (centre S.A) :=
    rationalSingularitySituationBlowUp_exceptionalIdeal S
  have hE : Stacks.Divisors.IsEffectiveCartierDivisor
      (rationalSingularitySituationBlowUp S).exceptionalIdeal := by
    rw [hid]
    exact Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal (centre S.A)
  have h := RationalSingularitySituation.idealSheafGlobalSections_exceptionalIdealPow_unconditional
    _ hE n
  rwa [hid] at h

/-! ### The sequence on global sections -/

/-- **`Γ(X, ℐⁿ) ⟶ Γ(E, 𝒪_E(n))` is surjective**: the long exact sequence of the restriction
sequence continues into `H¹(X, ℐⁿ⁺¹)`, which vanishes by [Stacks, Tag 0B4Y]. -/
theorem surjective_moduleGlobalSections_map_exceptionalTwistedSequence_g (n : ℕ) :
    Function.Surjective
      ((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
        (exceptionalTwistedSequence S.A n).g).hom := by
  have h₁ : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (blowUpScheme S.A)).rightDerived 1).obj (exceptionalTwistedSequence S.A n).X₁) := by
    have h : IsZero (((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (blowUpScheme S.A)).rightDerived 1).obj (idealSheafOfModules
          (exceptionalIdeal (centre S.A) * exceptionalIdeal (centre S.A) ^ n))) := by
      rw [← pow_succ']
      exact isZero_firstCohomology_exceptionalIdealPow S (n + 1)
    exact IsZero.of_iso h (((Stacks.Cohomology.AffineBase.moduleGlobalSections
      (blowUpScheme S.A)).rightDerived 1).mapIso (exceptionalTwistedSequenceIsoOne S.A n))
  have hepi :=
    Stacks.Cohomology.SectionsEpi.epi_moduleGlobalSections_map_of_isZero_rightDerived_one
      (blowUpScheme S.A) (shortExact_exceptionalTwistedSequence S.A n) h₁
  exact (ModuleCat.epi_iff_surjective _).1 hepi

/-- **The global sections of the restriction sequence are exact in the middle**: the range of
`Γ(X, ℐⁿ⁺¹) ⟶ Γ(X, ℐⁿ)` is the kernel of `Γ(X, ℐⁿ) ⟶ Γ(E, 𝒪_E(n))`. This is the long exact
sequence of the cohomological `δ`-functor of [Stacks, Tag 010Q] in degree zero, with
`CategoryTheory.Functor.rightDerivedZeroIsoSelf` identifying `R⁰Γ` with `Γ`. -/
theorem range_eq_ker_moduleGlobalSections_map_exceptionalTwistedSequence (n : ℕ) :
    LinearMap.range ((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
        (exceptionalTwistedSequence S.A n).f).hom =
      LinearMap.ker ((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (blowUpScheme S.A)).map (exceptionalTwistedSequence S.A n).g).hom := by
  have hex : ((exceptionalTwistedSequence S.A n).map
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A))).Exact :=
    ShortComplex.exact_of_iso
      (ShortComplex.mapNatIso (exceptionalTwistedSequence S.A n)
        (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)
          ).rightDerivedZeroIsoSelf)
      ((cohomologyDeltaFunctor (blowUpScheme S.A)).exact_map
        (shortExact_exceptionalTwistedSequence S.A n) 0)
  exact hex.moduleCat_range_eq_ker

/-! ### The first map on global sections is the inclusion `𝔪ⁿ⁺¹ ⊆ 𝔪ⁿ` -/

/-- `H⁰(X, ℐⁿ⁺¹) ≅ H⁰(X, ℐ·ℐⁿ)`, the global sections of the identification
`AlgebraicGeometry.BlowUpDualizing.exceptionalTwistedSequenceIsoOne`. -/
def exceptionalTwistedSequenceSectionsIsoOne (n : ℕ) :
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
        (exceptionalTwistedSequence S.A n).X₁ ≅
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
        (idealSheafOfModules (exceptionalIdeal (centre S.A) *
          exceptionalIdeal (centre S.A) ^ n)) :=
  (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).mapIso
    (exceptionalTwistedSequenceIsoOne S.A n)

/-- **The first map of the restriction sequence, on global sections, is the inclusion of ideals.**
This is `AlgebraicGeometry.BlowUpDualizing.exceptionalTwistedSequence_f_comp_idealInclusion` after
taking global sections. -/
theorem exceptionalIdealPowSections_square (n : ℕ) :
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
          (exceptionalTwistedSequence S.A n).f ≫ exceptionalIdealPowSections S n =
      (exceptionalTwistedSequenceSectionsIsoOne S n).hom ≫
        exceptionalIdealMulPowSections S n := by
  change (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
        (exceptionalTwistedSequence S.A n).f ≫
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
        (Stacks.Divisors.idealInclusion (exceptionalIdeal (centre S.A) ^ n)) =
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
        (exceptionalTwistedSequenceIsoOne S.A n).hom ≫
      (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
        (Stacks.Divisors.idealInclusion
          (exceptionalIdeal (centre S.A) * exceptionalIdeal (centre S.A) ^ n))
  refine Eq.trans (Functor.map_comp _ _ _).symm ?_
  refine Eq.trans (congrArg
    (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
    (exceptionalTwistedSequence_f_comp_idealInclusion S.A n)) ?_
  exact Functor.map_comp _ _ _

/-- The square of `exceptionalIdealPowSections_square`, on an element. -/
theorem exceptionalIdealPowSections_square_apply (n : ℕ)
    (z : (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
      (exceptionalTwistedSequence S.A n).X₁) :
    (exceptionalIdealPowSections S n).hom
        (((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).map
          (exceptionalTwistedSequence S.A n).f).hom z) =
      (exceptionalIdealMulPowSections S n).hom
        ((exceptionalTwistedSequenceSectionsIsoOne S n).hom.hom z) :=
  congrArg (fun q => ModuleCat.Hom.hom q z) (exceptionalIdealPowSections_square S n)

/-- **The range of `Γ(X, ℐⁿ⁺¹) ⟶ Γ(X, ℐⁿ)` is `𝔪ⁿ⁺¹`**, read inside `Γ(X, 𝒪_X)` through the
inclusion of `ℐⁿ`. -/
theorem mem_range_moduleGlobalSections_map_exceptionalTwistedSequence_f (n : ℕ)
    (y : (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
      (exceptionalTwistedSequence S.A n).X₂) :
    y ∈ LinearMap.range ((Stacks.Cohomology.AffineBase.moduleGlobalSections
        (blowUpScheme S.A)).map (exceptionalTwistedSequence S.A n).f).hom ↔
      (exceptionalIdealPowSections S n).hom y ∈
        Ideal.map (globalFunctionsRingHom S) (IsLocalRing.maximalIdeal S.A ^ (n + 1)) := by
  have hideal : Ideal.map (globalFunctionsRingHom S)
        (IsLocalRing.maximalIdeal S.A ^ (n + 1)) =
      idealSheafGlobalSections (exceptionalIdeal (centre S.A) *
        exceptionalIdeal (centre S.A) ^ n) := by
    rw [← idealSheafGlobalSections_exceptionalIdealPow_centre S (n + 1), pow_succ']
  rw [hideal]
  refine ⟨fun hy => ?_, fun hy => ?_⟩
  · obtain ⟨z, rfl⟩ := hy
    rw [exceptionalIdealPowSections_square_apply]
    exact (mem_range_exceptionalIdealMulPowSections S n _).1 ⟨_, rfl⟩
  · obtain ⟨w, hw⟩ := (mem_range_exceptionalIdealMulPowSections S n _).2 hy
    refine ⟨(exceptionalTwistedSequenceSectionsIsoOne S n).inv.hom w, ?_⟩
    refine injective_exceptionalIdealPowSections S n ?_
    rw [exceptionalIdealPowSections_square_apply]
    refine Eq.trans ?_ hw
    refine congrArg (exceptionalIdealMulPowSections S n).hom ?_
    exact congrArg (fun q => ModuleCat.Hom.hom q w)
      (exceptionalTwistedSequenceSectionsIsoOne S n).inv_hom_id

/-! ### `H⁰(X, ℐⁿ) = 𝔪ⁿ` -/

/-- **`H⁰(X, ℐⁿ) ≅ ψ(𝔪ⁿ)` as `Γ(X, 𝒪_X)`-modules.** The inclusion of the ideal sheaf is
injective on global sections and its range is the image of `𝔪ⁿ` by [Stacks, Tag 0B4Y]. -/
def exceptionalIdealPowSectionsEquivIdeal (n : ℕ) :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
        (exceptionalTwistedSequence S.A n).X₂) ≃ₗ[Γ(blowUpScheme S.A, ⊤)]
      (Ideal.map (globalFunctionsRingHom S) (IsLocalRing.maximalIdeal S.A ^ n) :
        Ideal Γ(blowUpScheme S.A, ⊤)) :=
  (LinearEquiv.ofInjective (exceptionalIdealPowSections S n).hom
      (injective_exceptionalIdealPowSections S n)).trans
    (LinearEquiv.ofEq _ _ (Submodule.ext fun a =>
      (mem_range_exceptionalIdealPowSections S n a).trans
        (by rw [idealSheafGlobalSections_exceptionalIdealPow_centre]; exact Iff.rfl)))

/-- The identification of `H⁰(X, ℐⁿ)` with `ψ(𝔪ⁿ)` reads a global section of `ℐⁿ` as a global
function. -/
theorem coe_exceptionalIdealPowSectionsEquivIdeal (n : ℕ)
    (y : (Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
      (exceptionalTwistedSequence S.A n).X₂) :
    ((exceptionalIdealPowSectionsEquivIdeal S n y : Γ(blowUpScheme S.A, ⊤))) =
      (exceptionalIdealPowSections S n).hom y :=
  rfl

/-! ### The quotient `H⁰(X, ℐⁿ)/H⁰(X, ℐⁿ⁺¹)` -/

/-- **The image of `H⁰(X, ℐⁿ⁺¹)` inside `ψ(𝔪ⁿ)` is `ψ(𝔪ⁿ⁺¹)`.** The first map of the restriction
sequence is the inclusion of ideal sheaves, so on global sections it is the inclusion
`𝔪ⁿ⁺¹ ⊆ 𝔪ⁿ`. -/
theorem map_exceptionalIdealPowSectionsEquivIdeal_range (n : ℕ) :
    Submodule.map (exceptionalIdealPowSectionsEquivIdeal S n).toLinearMap
        (LinearMap.range ((Stacks.Cohomology.AffineBase.moduleGlobalSections
          (blowUpScheme S.A)).map (exceptionalTwistedSequence S.A n).f).hom) =
      Submodule.comap (Ideal.map (globalFunctionsRingHom S)
          (IsLocalRing.maximalIdeal S.A ^ n) : Ideal Γ(blowUpScheme S.A, ⊤)).subtype
        (Ideal.map (globalFunctionsRingHom S) (IsLocalRing.maximalIdeal S.A ^ (n + 1))) := by
  refine Submodule.ext fun z => ?_
  have hz : (exceptionalIdealPowSections S n).hom
      ((exceptionalIdealPowSectionsEquivIdeal S n).symm z) =
      (z : Γ(blowUpScheme S.A, ⊤)) := by
    rw [← coe_exceptionalIdealPowSectionsEquivIdeal,
      (exceptionalIdealPowSectionsEquivIdeal S n).apply_symm_apply]
  rw [Submodule.mem_map_equiv, Submodule.mem_comap,
    mem_range_moduleGlobalSections_map_exceptionalTwistedSequence_f, hz]
  exact Iff.rfl

/-- **`H⁰(X, i_*𝒪_E(n)) ≅ ψ(𝔪ⁿ)/ψ(𝔪ⁿ⁺¹)`** as `Γ(X, 𝒪_X)`-modules: the restriction sequence is
exact on global sections, with `H¹(X, ℐⁿ⁺¹) = 0` making its last map surjective. -/
def curveSectionsEquivIdealQuotient (n : ℕ) :
    ((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).obj
        (exceptionalTwistedSequence S.A n).X₃) ≃ₗ[Γ(blowUpScheme S.A, ⊤)]
      ((Ideal.map (globalFunctionsRingHom S) (IsLocalRing.maximalIdeal S.A ^ n) :
          Ideal Γ(blowUpScheme S.A, ⊤)) ⧸
        Submodule.comap (Ideal.map (globalFunctionsRingHom S)
            (IsLocalRing.maximalIdeal S.A ^ n) : Ideal Γ(blowUpScheme S.A, ⊤)).subtype
          (Ideal.map (globalFunctionsRingHom S) (IsLocalRing.maximalIdeal S.A ^ (n + 1)))) :=
  (LinearMap.quotKerEquivOfSurjective _
        (surjective_moduleGlobalSections_map_exceptionalTwistedSequence_g S n)).symm.trans
    ((Submodule.quotEquivOfEq _ _
          (range_eq_ker_moduleGlobalSections_map_exceptionalTwistedSequence S n).symm).trans
      (Submodule.Quotient.equiv _ _ (exceptionalIdealPowSectionsEquivIdeal S n)
        (map_exceptionalIdealPowSectionsEquivIdeal_range S n)))

/-! ### Transport of a graded piece along the identification `A ≅ Γ(X, 𝒪_X)` -/

section GradedPiece

variable {A R : Type u} [CommRing A] [CommRing R] (f : A →+* R) (J K : Ideal A)

/-- `J ⟶ f(J)`, the map `f` induces on an ideal. -/
private def toMapIdeal (x : (J : Ideal A)) : (Ideal.map f J : Ideal R) :=
  ⟨f (x : A), Ideal.mem_map_of_mem f x.2⟩

/-- `J ⟶ f(J)` is surjective when `f` is bijective. -/
private theorem surjective_toMapIdeal (hf : Function.Bijective f) :
    Function.Surjective (toMapIdeal f J) := fun z => by
  obtain ⟨a, ha⟩ := hf.2 (z : R)
  exact ⟨⟨a, (mem_map_iff_of_bijective f hf J a).1 (ha ▸ z.2)⟩, Subtype.ext ha⟩

/-- **`J ⟶ f(J)/f(K)`**, the map `f` induces on graded pieces, read `A`-linearly: the scalars on
the target are restricted along `f`. -/
private def gradedPieceMap :
    (J : Ideal A) →ₗ[A] (ModuleCat.restrictScalars f).obj
      (ModuleCat.of R ((Ideal.map f J : Ideal R) ⧸
        Submodule.comap (Ideal.map f J : Ideal R).subtype (Ideal.map f K))) where
  toFun x := Submodule.Quotient.mk (toMapIdeal f J x)
  map_add' _ _ :=
    congrArg (Submodule.Quotient.mk (p := Submodule.comap
      (Ideal.map f J : Ideal R).subtype (Ideal.map f K))) (Subtype.ext (map_add f _ _))
  map_smul' _ _ :=
    congrArg (Submodule.Quotient.mk (p := Submodule.comap
      (Ideal.map f J : Ideal R).subtype (Ideal.map f K))) (Subtype.ext (map_mul f _ _))

/-- `J ⟶ f(J)/f(K)` is surjective when `f` is bijective. -/
private theorem surjective_gradedPieceMap (hf : Function.Bijective f) :
    Function.Surjective (gradedPieceMap f J K) :=
  (Submodule.mkQ_surjective _).comp (surjective_toMapIdeal f J hf)

/-- `J ⟶ f(J)/f(K)` kills exactly the elements of `J` lying in `K`, when `f` is bijective. -/
private theorem gradedPieceMap_eq_zero_iff (hf : Function.Bijective f) (x : (J : Ideal A)) :
    gradedPieceMap f J K x = 0 ↔ (x : A) ∈ K := by
  change (Submodule.Quotient.mk (p := Submodule.comap
    (Ideal.map f J : Ideal R).subtype (Ideal.map f K)) (toMapIdeal f J x) : _) = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  exact mem_map_iff_of_bijective f hf K _

/-- The kernel of `J ⟶ f(J)/f(K)` is the part of `K` inside `J`, when `f` is bijective. -/
private theorem ker_gradedPieceMap (hf : Function.Bijective f) :
    LinearMap.ker (gradedPieceMap f J K) = Submodule.comap (J : Ideal A).subtype K :=
  Submodule.ext fun x => by
    rw [LinearMap.mem_ker, gradedPieceMap_eq_zero_iff f J K hf, Submodule.mem_comap]
    exact Iff.rfl

/-- **Transport of a graded piece along a bijective ring homomorphism.** For `f : A ⟶ R`
bijective and ideals `J`, `K` of `A`, the graded piece `J/(K ∩ J)` of `A` is the graded piece
`f(J)/(f(K) ∩ f(J))` of `R` with scalars restricted along `f`. -/
private def gradedPieceEquiv (hf : Function.Bijective f) :
    ((J : Ideal A) ⧸ Submodule.comap (J : Ideal A).subtype K) ≃ₗ[A]
      (ModuleCat.restrictScalars f).obj
        (ModuleCat.of R ((Ideal.map f J : Ideal R) ⧸
          Submodule.comap (Ideal.map f J : Ideal R).subtype (Ideal.map f K))) :=
  (Submodule.quotEquivOfEq _ _ (ker_gradedPieceMap f J K hf).symm).trans
    (LinearMap.quotKerEquivOfSurjective _ (surjective_gradedPieceMap f J K hf))

end GradedPiece

/-- **`𝔪ⁿ⁺¹ ∩ 𝔪ⁿ = 𝔪·𝔪ⁿ`**, the two spellings of the submodule the graded piece is a quotient
by. -/
theorem comap_subtype_eq_smul_top {A : Type u} [CommRing A] (J : Ideal A) (n : ℕ) :
    Submodule.comap (J ^ n : Ideal A).subtype (J ^ (n + 1)) =
      (J • ⊤ : Submodule A (J ^ n : Ideal A)) :=
  Submodule.ext fun x => by
    rw [Submodule.mem_comap, mem_smul_top_iff]
    exact Iff.rfl

/-! ### Clause (5) -/

/-- **`H⁰(E, 𝒪_E(n)) = 𝔪ⁿ/𝔪ⁿ⁺¹` for every `n ≥ 0`.**

The global sections of the `n`-th twist on the exceptional curve, read as a module over `A`
through the structure morphism `E ⟶ X ⟶ Spec(A)`, are the `n`-th graded piece `𝔪ⁿ/𝔪ⁿ⁺¹` of the
maximal-ideal filtration. The quotient is written by the submodule `𝔪·𝔪ⁿ` of `𝔪ⁿ`, which is
`𝔪ⁿ⁺¹` by `AlgebraicGeometry.BlowUpDualizing.comap_subtype_eq_smul_top` and is the shape
`Ideal.Cotangent` uses.

This is read off the restriction sequence
`0 ⟶ ℐⁿ⁺¹ ⟶ ℐⁿ ⟶ i_*𝒪_E(n) ⟶ 0` and its long exact cohomology sequence: `H¹(X, ℐⁿ⁺¹) = 0` makes
`H⁰(X, ℐⁿ) ⟶ H⁰(X, i_*𝒪_E(n))` surjective, its kernel is the image of `H⁰(X, ℐⁿ⁺¹)`, and the
first map of the sequence is the inclusion of ideal sheaves, so that image is `𝔪ⁿ⁺¹` inside
`H⁰(X, ℐⁿ) = 𝔪ⁿ`. Both of the latter identifications are [Stacks, Tag 0B4Y]: `H¹(X, ℐⁿ⁺¹) = 0`
and `H⁰(X, ℐⁿ) = 𝔪ⁿ`. **No `H²` is used**, and no hypothesis beyond Situation
[Stacks, Tag 0B4W] is placed on `A`.

The cohomology on `E` is compared with the cohomology of the direct image on `X` by
[Stacks, Tag 01EZ] over the whole space
(`Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop`), and the `A`-module structure is the
restriction of scalars along `A ≅ Γ(X, 𝒪_X) ⟶ Γ(E, 𝒪_E)`, which
`ModuleCat.restrictScalarsComp'App` splits into the two steps. -/
@[stacks 0B63 "clause (5): H^0(E, O_E(n)) = m^n/m^(n+1) for every n >= 0"]
theorem nonempty_curveTwistSheafSections_iso_gradedPiece (n : ℕ) :
    Nonempty ((ModuleCat.restrictScalars
          ((Scheme.ΓSpecIso (.of S.A)).inv ≫
            (exceptionalImmersion S.A ≫ blowUpToBase (centre S.A)).appTop).hom).obj
        ((Stacks.Cohomology.AffineBase.moduleGlobalSections (exceptionalCurve S.A)).obj
          (curveTwistSheaf S.A (n : ℤ))) ≅
      ModuleCat.of S.A ((IsLocalRing.maximalIdeal S.A ^ n : Ideal S.A) ⧸
        (IsLocalRing.maximalIdeal S.A • ⊤ :
          Submodule S.A (IsLocalRing.maximalIdeal S.A ^ n : Ideal S.A)))) := by
  have hcomp : ((Scheme.ΓSpecIso (.of S.A)).inv ≫
        (exceptionalImmersion S.A ≫ blowUpToBase (centre S.A)).appTop).hom =
      ((exceptionalImmersion S.A).appTop.hom).comp (globalFunctionsRingHom S) := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc]
    rfl
  refine ⟨ModuleCat.restrictScalarsComp'App (globalFunctionsRingHom S)
      (exceptionalImmersion S.A).appTop.hom _ hcomp _ ≪≫
    (ModuleCat.restrictScalars (globalFunctionsRingHom S)).mapIso
        ((Stacks.Cohomology.AffineBase.sectionsRestrictionIsoTop
          (exceptionalImmersion S.A)).app (curveTwistSheaf S.A (n : ℤ))) ≪≫
    (ModuleCat.restrictScalars (globalFunctionsRingHom S)).mapIso
        ((Stacks.Cohomology.AffineBase.moduleGlobalSections (blowUpScheme S.A)).mapIso
          (exceptionalTwistedSequenceIsoThree S.A n).symm) ≪≫
    (ModuleCat.restrictScalars (globalFunctionsRingHom S)).mapIso
        (curveSectionsEquivIdealQuotient S n).toModuleIso ≪≫
    (gradedPieceEquiv (globalFunctionsRingHom S) (IsLocalRing.maximalIdeal S.A ^ n)
        (IsLocalRing.maximalIdeal S.A ^ (n + 1))
        (bijective_globalFunctionsRingHom S)).symm.toModuleIso ≪≫
    (Submodule.quotEquivOfEq _ _
        (comap_subtype_eq_smul_top (IsLocalRing.maximalIdeal S.A) n)).toModuleIso⟩

end AlgebraicGeometry.BlowUpDualizing

end
