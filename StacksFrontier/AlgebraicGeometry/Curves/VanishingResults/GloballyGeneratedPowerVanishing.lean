module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.ComponentPositivity
public import StacksFrontier.AlgebraicGeometry.AmpleFromAffineNonvanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.Idempotents
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalTails.RationalTail
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistCanonical
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullback
public import StacksFrontier.Topology.Sheaves.Modules.FiniteType

/-!
# Globally generated powers of an invertible module on a proper curve

Let `k` be a field and `X` a proper scheme over `k` of dimension at most one. This file collects
what global generation of a power `ℒ^{⊗ m}`, `m > 0`, of an invertible `𝒪_X`-module says about
the degrees of `ℒ` and about the cohomology of the powers of `ℒ`.

* A globally generated invertible module on a proper integral curve has a global section that
  does not vanish identically, hence nonnegative degree ([Stacks, Tag 0B40], part (1)). Pulling
  generating sections back along a morphism `Y ⟶ X` from a proper integral curve, and using
  `deg((ℒ^{⊗ m})|_Y) = m · deg(ℒ|_Y)`, the same holds for `deg(ℒ|_Y)` as soon as some positive
  power of `ℒ` is globally generated. In particular `deg(ℒ|_C) ≥ 0` for every rational tail `C`
  of `X` ([Stacks, Tag 0E3H]).
* If moreover `X` is reduced, connected and equidimensional of dimension one and `deg(ℒ) > 0`,
  then every negative power of `ℒ` has degree `≤ 0` on every irreducible component and negative
  total degree, so it has no nonzero global sections ([Stacks, Tag 0E22]).
* At the dualizing sheaf `ω_X` of [Stacks, Tag 0BS2], assumed invertible and of positive degree,
  duality turns the vanishing of `H⁰(X, ω_X^{⊗ 1 - m})` into the vanishing of
  `H¹(X, ω_X^{⊗ m})` for every `m ≥ 2` for which `ω_X^{⊗ m}` is globally generated.

These are the curve-theoretic steps of the proof of [Stacks, Tag 0E6Y]: the first is the step
by which global generation of `ω_{X_s}^{⊗ m}` excludes rational tails, the last the vanishing
`H¹(X_s, ω_{X_s}^{⊗ m}) = 0` in genus at least two, where `deg(ω_{X_s}) = 2g - 2 > 0`.

## Main results

* `invertibleCurveDegree_nonneg_of_generatingSections`: a globally generated invertible module
  on a proper integral curve has nonnegative degree.
* `invertibleCurveDegree_modulePullback_nonneg_of_generatingSections_tensorPower`: if `ℒ^{⊗ m}`
  is globally generated for some `m > 0`, then `deg(ℒ|_Y) ≥ 0` for every morphism `Y ⟶ X` from a
  proper integral curve.
* `IsRationalTail.invertibleCurveDegree_nonneg_of_generatingSections_tensorPower`: the same for
  the restriction of `ℒ` to a rational tail.
* `subsingleton_globalSections_of_invertibleCurveDegree_neg`: an invertible module of degree `≤ 0`
  on every irreducible component and of negative degree has no nonzero global sections.
* `subsingleton_globalSections_tensorPower_of_generatingSections`: if `ℒ^{⊗ m}` is globally
  generated for some `m > 0` and `deg(ℒ) > 0`, then `H⁰(X, ℒ^{⊗ n}) = 0` for every `n < 0`.
* `CohenMacaulayCurveSituation.isZero_cohomologyOverField_one_dualizingSheafOverField_tensorPower`:
  `H¹(X, ω_X^{⊗ m}) = 0` when `ω_X` is invertible of positive degree, `m ≥ 2` and `ω_X^{⊗ m}` is
  globally generated.

## Implementation notes

The restriction of a module to a subcurve is the pullback
`RingedSpaceModuleAdjunction.modulePullback` along the morphism of ringed spaces underlying the
closed immersion, the spelling in which [Stacks, Tag 0E22] states its degree hypothesis, and the
integral tensor powers are `Stacks.SheafOfModules.Invertible.tensorPower`. Global generation is
the existence of a `SheafOfModules.GeneratingSections`.

## References

* [Stacks Project, Tag 0E6Y](https://stacks.math.columbia.edu/tag/0E6Y)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0E22](https://stacks.math.columbia.edu/tag/0E22)
* [Stacks Project, Tag 0E3H](https://stacks.math.columbia.edu/tag/0E3H)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS3](https://stacks.math.columbia.edu/tag/0BS3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k]

/-! ### Nonnegativity of degrees -/

/-- **A globally generated invertible module on a proper integral curve has nonnegative
degree.** Some member of a generating family does not vanish at a given point, so it is a
nonzero global section, and [Stacks, Tag 0B40] part (1) applies. -/
theorem invertibleCurveDegree_nonneg_of_generatingSections {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsIntegral X]
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (σ : L.GeneratingSections) :
    0 ≤ invertibleCurveDegree k f hdim L := by
  obtain ⟨x⟩ : Nonempty X := inferInstance
  have := Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ L
  have : SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := hL
  obtain ⟨i, hi⟩ := Stacks.SheafOfModules.exists_generatingSection_nonvanishing L σ x
  exact invertibleCurveDegree_nonneg_of_eval_top_ne_zero k f hdim L (σ.s i)
    (eval_top_ne_zero_of_mem_nonvanishingLocus L _ hi)

/-- The degree of the restriction of an integral tensor power is the power times the degree
of the restriction: pullback commutes with the integral tensor powers. -/
private theorem invertibleCurveDegree_modulePullback_tensorPower_eq_mul {X Y : Scheme.{u}}
    (i : Y ⟶ X) (g : Y ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim Y ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (n : ℤ)
    [hP : SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 L n))]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L)] :
    invertibleCurveDegree k g hdim
        ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj
          (tensorPower X.presheaf X.ringCatSheaf.2 L n)) =
      n * invertibleCurveDegree k g hdim
        ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L) := by
  have hT := tensorPower_isInvertible Y.presheaf Y.ringCatSheaf.2
    ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L) n
  have e : (RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj
      (tensorPower X.presheaf X.ringCatSheaf.2 L n) ≅
      tensorPower Y.presheaf Y.ringCatSheaf.2
        ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L) n :=
    Stacks.TensorPowerPullback.pullbackIntPowIso i.toLRSHom.toShHom L n
  rw [@invertibleCurveDegree_eq_of_iso k _ Y g _ hdim _ _ hP hT e]
  exact invertibleCurveDegree_tensorPower_eq_mul_of_topologicalKrullDim_le_one k g hdim _ n

/-- A negative power of an invertible module whose restriction to a proper curve has nonnegative
degree has nonpositive degree on that curve. -/
private theorem invertibleCurveDegree_modulePullback_tensorPower_nonpos {X Y : Scheme.{u}}
    (i : Y ⟶ X) (g : Y ⟶ Spec (.of k)) [IsProper g] (hdim : topologicalKrullDim Y ≤ 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {n : ℤ}
    (hn : n ≤ 0)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 L n))]
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L)]
    (h0 : 0 ≤ invertibleCurveDegree k g hdim
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L)) :
    invertibleCurveDegree k g hdim
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj
        (tensorPower X.presheaf X.ringCatSheaf.2 L n)) ≤ 0 := by
  rw [invertibleCurveDegree_modulePullback_tensorPower_eq_mul k i g hdim L n]
  exact mul_nonpos_of_nonpos_of_nonneg hn h0

/-- **The restriction of a globally generated invertible module to a proper integral curve
has nonnegative degree**: generating sections pull back to generating sections. -/
theorem invertibleCurveDegree_modulePullback_nonneg_of_generatingSections {X Y : Scheme.{u}}
    (i : Y ⟶ X) (g : Y ⟶ Spec (.of k)) [IsProper g] [IsIntegral Y]
    (hdim : topologicalKrullDim Y ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (σ : L.GeneratingSections)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L)] :
    0 ≤ invertibleCurveDegree k g hdim
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L) :=
  invertibleCurveDegree_nonneg_of_generatingSections k g hdim _
    (Stacks.SheafOfModules.modulePullbackGeneratingSections _ L σ)

/-- **If a positive power `ℒ^{⊗ m}` of an invertible module is globally generated, then the
restriction of `ℒ` to a proper integral curve has nonnegative degree**: the restriction of
`ℒ^{⊗ m}` has nonnegative degree, and that degree is `m` times the degree of the restriction
of `ℒ`. -/
theorem invertibleCurveDegree_modulePullback_nonneg_of_generatingSections_tensorPower
    {X Y : Scheme.{u}} (i : Y ⟶ X) (g : Y ⟶ Spec (.of k)) [IsProper g] [IsIntegral Y]
    (hdim : topologicalKrullDim Y ≤ 1) (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {m : ℤ} (hm : 0 < m)
    (σ : (tensorPower X.presheaf X.ringCatSheaf.2 L m).GeneratingSections)
    [SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L)] :
    0 ≤ invertibleCurveDegree k g hdim
      ((RingedSpaceModuleAdjunction.modulePullback i.toLRSHom.toShHom).obj L) := by
  have := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 L m
  have := RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme i
    (tensorPower X.presheaf X.ringCatSheaf.2 L m)
  have h := invertibleCurveDegree_modulePullback_nonneg_of_generatingSections k i g hdim _ σ
  rw [invertibleCurveDegree_modulePullback_tensorPower_eq_mul k i g hdim L m] at h
  by_contra hneg
  exact absurd h (not_le.mpr (mul_neg_of_pos_of_neg hm (not_le.mp hneg)))

/-- **If a positive power `ℒ^{⊗ m}` of an invertible module on a proper one-dimensional scheme
over `k` is globally generated, then `ℒ` has nonnegative degree on every rational tail.** This
is the step of [Stacks, Tag 0E6Y] by which global generation of a power of the dualizing sheaf
excludes rational tails, on which the dualizing sheaf has negative degree. -/
theorem IsRationalTail.invertibleCurveDegree_nonneg_of_generatingSections_tensorPower
    {X : Scheme.{u}} [X.Over (Spec (.of k))] [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X ≤ 1) {C : X.IdealSheafData} (hC : IsRationalTail k X C)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {m : ℤ}
    (hm : 0 < m) (σ : (tensorPower X.presheaf X.ringCatSheaf.2 L m).GeneratingSections) :
    haveI := RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme C.subschemeι L
    0 ≤ invertibleCurveDegree k (C.subschemeι ≫ (X ↘ Spec (.of k)))
      ((StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion C.subschemeι).trans hdim)
      ((RingedSpaceModuleAdjunction.modulePullback C.subschemeι.toLRSHom.toShHom).obj L) := by
  have := RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme C.subschemeι L
  have : IsIntegral C.subscheme := hC.isIntegral
  exact invertibleCurveDegree_modulePullback_nonneg_of_generatingSections_tensorPower k
    C.subschemeι _ _ L hm σ

/-! ### Vanishing of global sections of negative powers -/

/-- **An invertible module of nonpositive degree on every irreducible component and of
negative degree has no nonzero global sections.** By [Stacks, Tag 0E22] it either has no
nonzero global sections or is trivial, and a trivial module has degree zero. -/
theorem subsingleton_globalSections_of_invertibleCurveDegree_neg {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X] [ConnectedSpace X]
    (hequi : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (hdeg : ∀ (C : Set X) (hC : C ∈ irreducibleComponents X),
      haveI := RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme
        (Scheme.IdealSheafData.vanishingIdeal
          ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι L
      invertibleCurveDegree k
          ((Scheme.IdealSheafData.vanishingIdeal
            ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι ≫ f)
          ((StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι).trans hdim.le)
          ((RingedSpaceModuleAdjunction.modulePullback
            (Scheme.IdealSheafData.vanishingIdeal
              ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩).subschemeι.toLRSHom.toShHom).obj
            L) ≤ 0)
    (hneg : invertibleCurveDegree k f hdim.le L < 0) :
    Subsingleton Γ(L, ⊤) := by
  rcases subsingleton_globalSections_or_isTrivial_of_invertibleCurveDegree_nonpos k f hequi hdim
    L hdeg with h | h
  · exact h
  · obtain ⟨e⟩ := h
    exact absurd (invertibleCurveDegree_eq_zero_of_iso_unit k f hdim.le L e) hneg.ne

/-- **If a positive power of an invertible module of positive degree is globally generated,
then its negative powers have no nonzero global sections.** On a proper scheme over `k` which is
reduced, connected and equidimensional of dimension one, let `ℒ^{⊗ m}`, `m > 0`, be globally
generated and `deg(ℒ) > 0`. For `n < 0` the restriction of `ℒ^{⊗ n}` to an irreducible
component `C` has degree `n · deg(ℒ|_C) ≤ 0`, because `deg(ℒ|_C) ≥ 0`, and `ℒ^{⊗ n}` has degree
`n · deg(ℒ) < 0`. -/
theorem subsingleton_globalSections_tensorPower_of_generatingSections {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X] [ConnectedSpace X]
    (hequi : TopologicalSpace.Equidimensional X) (hdim : topologicalKrullDim X = 1)
    (L : X.Modules) [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {m : ℤ}
    (hm : 0 < m) (σ : (tensorPower X.presheaf X.ringCatSheaf.2 L m).GeneratingSections)
    (hpos : 0 < invertibleCurveDegree k f hdim.le L) {n : ℤ} (hn : n < 0) :
    haveI := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 L n
    Subsingleton Γ(tensorPower X.presheaf X.ringCatSheaf.2 L n, ⊤) := by
  have := tensorPower_isInvertible X.presheaf X.ringCatSheaf.2 L n
  refine subsingleton_globalSections_of_invertibleCurveDegree_neg k f hequi hdim _
    (fun C hC => ?_) ?_
  · let Z := Scheme.IdealSheafData.vanishingIdeal
      ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩
    have : IsIntegral Z.subscheme :=
      StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
        hC.1
    have := RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme Z.subschemeι L
    have := RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme Z.subschemeι
      (tensorPower X.presheaf X.ringCatSheaf.2 L n)
    have hdimZ : topologicalKrullDim Z.subscheme ≤ 1 :=
      (StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion Z.subschemeι).trans hdim.le
    have h0 := invertibleCurveDegree_modulePullback_nonneg_of_generatingSections_tensorPower k
      Z.subschemeι (Z.subschemeι ≫ f) hdimZ L hm σ
    exact invertibleCurveDegree_modulePullback_tensorPower_nonpos k Z.subschemeι _ hdimZ L
      hn.le h0
  · rw [invertibleCurveDegree_tensorPower_eq_mul_of_topologicalKrullDim_le_one k f hdim.le L n]
    exact mul_neg_of_neg_of_pos hn hpos

/-! ### Vanishing of the first cohomology of powers of the dualizing sheaf -/

namespace CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-- In Situation [Stacks, Tag 0B5D] the curve is connected: its global functions form the
field `k`, which has no nontrivial idempotents. -/
theorem connectedSpace : ConnectedSpace S.X := by
  have : IsIso S.f.appTop :=
    (IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (CommRingCat.of S.k)).inv S.f.appTop :)
  exact Stacks.AmpleSectionConnected.connectedSpace_of_bijective_appTop S.f
    (ConcreteCategory.bijective_of_isIso S.f.appTop)

/-- **`H¹(X, ω_X^{⊗ m}) = 0` when `ω_X^{⊗ m}` is globally generated, `m ≥ 2`, and `ω_X` is
invertible of positive degree.** In Situation [Stacks, Tag 0B5D] with `X` reduced and
equidimensional, let `ω_X` be the dualizing sheaf of [Stacks, Tag 0BS2]. The negative power
`(ω_X^{⊗ m - 1})^{⊗ -1}` has degree `-(m - 1) · deg(ω_X|_C) ≤ 0` on every irreducible component
`C`, as `ω_X^{⊗ m}` is globally generated, and negative total degree, so it has no nonzero
global sections ([Stacks, Tag 0E22]); by duality
(`AlgebraicGeometry.CohenMacaulayCurveSituation.dualityVanishing_dualizingSheafOverField`)
`H¹(X, ω_X ⊗ ω_X^{⊗ m - 1}) = 0`, and `ω_X ⊗ ω_X^{⊗ m - 1} ≅ ω_X^{⊗ m}`.

This is the vanishing in the genus `≥ 2` case of the proof of [Stacks, Tag 0E6Y], where
`deg(ω_X) = 2g - 2 > 0`. -/
theorem isZero_cohomologyOverField_one_dualizingSheafOverField_tensorPower [IsReduced S.X]
    (hequi : TopologicalSpace.Equidimensional S.X)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField S.f)]
    (hpos : 0 < invertibleCurveDegree S.k S.f S.dimension_one.le
      (Stacks.Duality.dualizingSheafOverField S.f))
    {m : ℤ} (hm : 2 ≤ m)
    (σ : (tensorPower S.X.presheaf S.X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField S.f) m).GeneratingSections) :
    haveI := tensorPower_isInvertible S.X.presheaf S.X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField S.f) m
    IsZero (cohomologyOverField S.k S.f (tensorPower S.X.presheaf S.X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField S.f) m) 1) := by
  have := S.connectedSpace
  set ω := Stacks.Duality.dualizingSheafOverField S.f
  have hM := tensorPower_isInvertible S.X.presheaf S.X.ringCatSheaf.2 ω (m - 1)
  set M := tensorPower S.X.presheaf S.X.ringCatSheaf.2 ω (m - 1)
  have := tensorPower_isInvertible S.X.presheaf S.X.ringCatSheaf.2 M (-1)
  have hm0 : (0 : ℤ) < m := by omega
  have hm1 : (0 : ℤ) < m - 1 := by omega
  -- `H⁰(X, M^{⊗ -1}) = 0`.
  have hH0 : Subsingleton Γ(tensorPower S.X.presheaf S.X.ringCatSheaf.2 M (-1), ⊤) := by
    refine subsingleton_globalSections_of_invertibleCurveDegree_neg S.k S.f hequi
      S.dimension_one _ (fun C hC => ?_) ?_
    · let Z := Scheme.IdealSheafData.vanishingIdeal
        ⟨C, isClosed_of_mem_irreducibleComponents C hC⟩
      have : IsIntegral Z.subscheme :=
        StacksTag09NX.isIntegral_subscheme_vanishingIdeal_of_isIrreducible _
          hC.1
      have := RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme Z.subschemeι ω
      have := RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme Z.subschemeι M
      have := RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme Z.subschemeι
        (tensorPower S.X.presheaf S.X.ringCatSheaf.2 M (-1))
      have hdimZ : topologicalKrullDim Z.subscheme ≤ 1 :=
        (StacksTag09NX.topologicalKrullDim_le_of_isClosedImmersion Z.subschemeι).trans
          S.dimension_one.le
      have h0 := invertibleCurveDegree_modulePullback_nonneg_of_generatingSections_tensorPower
        S.k Z.subschemeι (Z.subschemeι ≫ S.f) hdimZ ω hm0 σ
      refine invertibleCurveDegree_modulePullback_tensorPower_nonpos S.k Z.subschemeι _ hdimZ M
        (by norm_num) ?_
      rw [invertibleCurveDegree_modulePullback_tensorPower_eq_mul S.k Z.subschemeι _ hdimZ ω]
      exact mul_nonneg hm1.le h0
    · rw [invertibleCurveDegree_tensorPower_eq_mul_of_topologicalKrullDim_le_one S.k S.f
        S.dimension_one.le M (-1),
        invertibleCurveDegree_tensorPower_eq_mul_of_topologicalKrullDim_le_one S.k S.f
        S.dimension_one.le ω (m - 1)]
      nlinarith
  -- Duality: `H¹(X, ω ⊗ M) = 0`.
  have hH1 := S.dualityVanishing_dualizingSheafOverField M hH0
  -- `ω ⊗ M ≅ ω^{⊗ m}`.
  let e : ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf (forget₂ CommRingCat RingCat)
        S.X.ringCatSheaf.property⟩).obj ω).obj M ≅
      tensorPower S.X.presheaf S.X.ringCatSheaf.2 ω m :=
    ((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ S.X.presheaf (forget₂ CommRingCat RingCat)
        S.X.ringCatSheaf.property⟩).flip.obj M).mapIso
        (Stacks.SheafOfModules.TensorPower.tensorPowerOneIso S.X.presheaf
          S.X.ringCatSheaf.2 ω).symm ≪≫
      Stacks.SheafOfModules.TensorPower.tensorPowerMulIso S.X.presheaf S.X.ringCatSheaf.2 ω 1
        (m - 1) ≪≫
      eqToIso (by rw [show (1 : ℤ) + (m - 1) = m by omega]; rfl)
  exact hH1.of_iso ((ModuleCat.restrictScalars _).mapIso
    (((SheafOfModules.evaluation S.X.ringCatSheaf (op ⊤)).rightDerived 1).mapIso e.symm))

end CohenMacaulayCurveSituation

end AlgebraicGeometry

end
