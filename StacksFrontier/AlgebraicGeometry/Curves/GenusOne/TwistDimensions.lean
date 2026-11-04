module

public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveAmple
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.AmplePullbackPart1.TensorPowerTensor
public import StacksFrontier.AlgebraicGeometry.Curves.GenusOne.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.LargeDegreeVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorTwistDegree
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.DivisorFirstDifference
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.MultiplePointSectionDimension

/-!
# Riemann–Roch dimension counts on a curve of genus one

Let `k` be a field and `f : X ⟶ Spec k` proper and smooth of relative dimension one, with
`dim_k H⁰(X, 𝒪_X) = 1` and genus one, and let `p` be a `k`-rational point of `X`. Riemann–Roch
reads `dim_k H⁰(X, ℒ) - dim_k H¹(X, ℒ) = deg ℒ` on such a curve, because the two correction
terms `dim_k H⁰(X, 𝒪_X)` and `g` cancel. This file records the consequences of that identity used
to analyse `X` through the tensor powers of an invertible module of positive degree, and computes
the degree of the divisor `n · p`.

## Main results

* `AlgebraicGeometry.GenusOne.finiteDimensional_cohomologyOverField_natTensorPow`: the
  cohomology of every tensor power of an invertible module is finite dimensional.
* `AlgebraicGeometry.GenusOne.mul_le_finrank_cohomologyOverField_zero_natTensorPow`:
  `d · m ≤ dim_k H⁰(X, ℒ^{⊗ m})` for `ℒ` of degree `d`.
* `AlgebraicGeometry.GenusOne.exists_forall_isZero_cohomologyOverField_one_natTensorPow`: for
  `ℒ` of positive degree, `H¹(X, ℒ^{⊗ m}) = 0` for every large `m`.
* `AlgebraicGeometry.GenusOne.exists_forall_finrank_cohomologyOverField_zero_natTensorPow_eq`:
  for `ℒ` of degree `d > 0`, `dim_k H⁰(X, ℒ^{⊗ m}) = d · m` for every large `m`.
* `AlgebraicGeometry.GenusOne.finrank_globalSections_eq_one_of_section`: an integral scheme
  universally closed over `k` with a `k`-rational point has `Γ(Z, 𝒪_Z) = k`.
* `AlgebraicGeometry.GenusOne.divisorInvertibleDegree_vanishingIdeal_point_pow`: the divisor
  `n · p` has degree `n`.
* `AlgebraicGeometry.GenusOne.invertibleCurveDegree_vanishingIdeal_point_pow`: the same for the
  degree of the invertible module `𝒪_X(n · p)`.

## Implementation notes

**Tensor powers.** The powers in the statements are the iterated powers
`Stacks.TensorPowers.natTensorPow`, for the monoidal structure on `X.Modules` used by
`StacksFrontier/AlgebraicGeometry/Curves/GenusOne/SectionRing.lean`. The library's degree and
vanishing theorems are stated over the integer powers
`Stacks.SheafOfModules.Invertible.tensorPower`; the two are compared by
`Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso` and
`Stacks.AmplePullbackPart1.natTensorPowIsoTensorPowModule`, and dimensions of cohomology are
carried along the comparison by `AlgebraicGeometry.cohomologyOverFieldIso`.

**Serre vanishing.** A module of positive degree is ample by [Stacks, Tag 0B5X], and the
implication (1) ⟹ (2) of [Stacks, Tag 0B5U] at the structure sheaf kills `H¹` of its large
powers.

**The degree of the point.** The degree of `𝒪_X(D)` is `dim_k Γ(D, 𝒪_D)`
(`AlgebraicGeometry.curveDegree_invertibleSheaf_eq_finrank_globalSections`). For the reduced point
`D = x`, the subscheme is integral and proper over `k`, so `Γ(D, 𝒪_D)` is a field finite over
`k`; the section `p` factors through `D` because `Spec k` is reduced with image `{x}`, and the
factorisation is a `k`-point of `D`, which splits `k ⟶ Γ(D, 𝒪_D)`. Multiplicativity in `n` is
`AlgebraicGeometry.divisorInvertibleDegree_pow_succ`.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 0B5U](https://stacks.math.columbia.edu/tag/0B5U)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.TensorPowers (natTensorPow)
open Stacks.SheafOfModules.Invertible (tensorPower tensorPower_isInvertible)
open Stacks.Divisors

universe u

namespace AlgebraicGeometry.GenusOne

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### Comparing the two families of tensor powers -/

/-- The integer tensor power `ℒ^{⊗ m}` of [Stacks, Tag 01CU] in nonnegative degree is the
iterated tensor power. -/
def tensorPowerIsoNatTensorPow (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L] (m : ℕ) :
    tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L (m : ℤ)
      ≅ natTensorPow (C := X.Modules) L m :=
  Stacks.PowerFamilyBridge.invertibleTensorPowerModuleIso X L (m : ℤ) ≪≫
    (Stacks.AmplePullbackPart1.natTensorPowIsoTensorPowModule X L m).symm

/-- **The cohomology of a tensor power of an invertible module is finite dimensional** on a
scheme proper over a field: the power is invertible, hence coherent. -/
theorem finiteDimensional_cohomologyOverField_natTensorPow [IsProper f] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (m n : ℕ) :
    FiniteDimensional k (cohomologyOverField k f (natTensorPow L m) n) := by
  have := tensorPower_isInvertible X.toRingedSpace.presheaf
    (structureSheafRing X.toRingedSpace).property L (m : ℤ)
  have hcoh := SheafOfModules.isCoherent_of_isInvertible k f
    (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L (m : ℤ))
  have := forall_finiteDimensional_cohomologyOverField_of_isProper k f _ hcoh n
  exact LinearEquiv.finiteDimensional
    (cohomologyOverFieldIso k f (tensorPowerIsoNatTensorPow L m) n).toLinearEquiv

/-- `dim_k H⁰(X, 𝒪_X) = 1` and `dim_k H¹(X, 𝒪_X) = 1`, read off the hypotheses at the spelling
`AlgebraicGeometry.cohomologyOverField`. -/
theorem finrank_cohomologyOverField_unit (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (hg : genus f = 1) :
    Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 0) = 1 ∧
      Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) 1) = 1 := by
  refine ⟨?_, ?_⟩
  · rw [← (structureSheafCohomologyIsoCohomologyOverField k f 0).toLinearEquiv.finrank_eq, h0]
  · rw [← (structureSheafCohomologyIsoCohomologyOverField k f 1).toLinearEquiv.finrank_eq,
      ← genus_eq_finrank_structureSheafCohomology, hg]

/-- **Riemann–Roch on a curve of genus one, for the tensor powers of an invertible module**:
`dim_k H⁰(X, ℒ^{⊗ m}) - dim_k H¹(X, ℒ^{⊗ m}) = m · deg ℒ`. The degree of `ℒ^{⊗ m}` is
`m · deg ℒ` ([Stacks, Tag 0AYX]) and the correction `dim_k H⁰(X, 𝒪_X) - g` vanishes. -/
theorem finrank_cohomologyOverField_zero_sub_one_natTensorPow [IsProper f]
    [SmoothOfRelativeDimension 1 f] (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (hg : genus f = 1) (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (m : ℕ) :
    (Module.finrank k (cohomologyOverField k f (natTensorPow L m) 0) : ℤ) -
        (Module.finrank k (cohomologyOverField k f (natTensorPow L m) 1) : ℤ) =
      (m : ℤ) * invertibleCurveDegree k f hdim L := by
  have := isCurve f h0
  obtain ⟨hO0, -⟩ := finrank_cohomologyOverField_unit f h0 hg
  have hdeg := invertibleCurveDegree_tensorPower_eq_mul_of_isCurve k f hdim L (m : ℤ)
  have hRR := finrank_cohomologyOverField_zero_sub_one_eq k f hdim
    (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L (m : ℤ))
    (tensorPower_isInvertible X.toRingedSpace.presheaf
      (structureSheafRing X.toRingedSpace).property L (m : ℤ))
  rw [hO0, hg] at hRR
  rw [← finrank_cohomologyOverField_eq_of_iso k f (tensorPowerIsoNatTensorPow L m) 0,
    ← finrank_cohomologyOverField_eq_of_iso k f (tensorPowerIsoNatTensorPow L m) 1]
  push_cast at hRR
  linarith

/-- **`d · m ≤ dim_k H⁰(X, ℒ^{⊗ m})`** for an invertible module `ℒ` of degree `d` on a curve of
genus one, by Riemann–Roch, discarding `dim_k H¹(X, ℒ^{⊗ m}) ≥ 0`. -/
theorem mul_le_finrank_cohomologyOverField_zero_natTensorPow [IsProper f]
    [SmoothOfRelativeDimension 1 f] (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (hg : genus f = 1) (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (hd : invertibleCurveDegree k f hdim L = d)
    (m : ℕ) : d * m ≤ Module.finrank k (cohomologyOverField k f (natTensorPow L m) 0) := by
  have h := finrank_cohomologyOverField_zero_sub_one_natTensorPow f h0 hg hdim L m
  rw [hd] at h
  zify
  linarith [Int.natCast_nonneg
    (Module.finrank k (cohomologyOverField k f (natTensorPow L m) 1))]

/-- **Serre vanishing for the powers of a module of positive degree**: on a curve of genus one —
indeed on any proper curve with `dim_k H⁰(X, 𝒪_X) = 1` — an invertible module of positive degree
has `H¹(X, ℒ^{⊗ m}) = 0` for every large `m`. It is ample by [Stacks, Tag 0B5X], and the
implication (1) ⟹ (2) of [Stacks, Tag 0B5U] applies to the structure sheaf. -/
theorem exists_forall_isZero_cohomologyOverField_one_natTensorPow [IsProper f]
    [SmoothOfRelativeDimension 1 f] (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules) [Stacks.Ample.IsInvertibleModule X L]
    (hpos : 0 < invertibleCurveDegree k f hdim L) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m → IsZero (cohomologyOverField k f (natTensorPow L m) 1) := by
  have := isCurve f h0
  have hOcoh : (SheafOfModules.unit X.ringCatSheaf : X.Modules).IsCoherent :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k f
  obtain ⟨m₀, hm₀⟩ :=
    Scheme.Modules.hasEventualTwistCohomologyVanishing_of_isAmple L f
      ((isAmple_iff_invertibleCurveDegree_pos k f hdim L).mpr hpos) _ hOcoh
  refine ⟨m₀, fun m hm => ?_⟩
  have e : ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, Presheaf.isSheaf_of_isSheaf_comp _ X.presheaf
          (forget₂ CommRingCat RingCat) X.ringCatSheaf.2⟩).obj
        (SheafOfModules.unit X.ringCatSheaf)).obj
      (tensorPower X.toRingedSpace.presheaf (structureSheafRing X.toRingedSpace).property L
        (m : ℤ))) : X.Modules) ≅ natTensorPow (C := X.Modules) L m :=
    Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.presheaf X.ringCatSheaf.2 _ ≪≫
      tensorPowerIsoNatTensorPow L m
  exact (isZero_cohomologyOverField_of_isZero_rightDerived k f _ 1
    (hm₀ m 1 hm Nat.one_pos)).of_iso (cohomologyOverFieldIso k f e 1).symm

/-- **`dim_k H⁰(X, ℒ^{⊗ m}) = d · m` for every large `m`**, for an invertible module `ℒ` of degree
`d > 0` on a curve of genus one: Riemann–Roch together with the eventual vanishing of
`H¹(X, ℒ^{⊗ m})`. -/
theorem exists_forall_finrank_cohomologyOverField_zero_natTensorPow_eq [IsProper f]
    [SmoothOfRelativeDimension 1 f] (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (hg : genus f = 1) (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (hd : invertibleCurveDegree k f hdim L = d)
    (hpos : 0 < d) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      Module.finrank k (cohomologyOverField k f (natTensorPow L m) 0) = d * m := by
  obtain ⟨m₀, hm₀⟩ := exists_forall_isZero_cohomologyOverField_one_natTensorPow f h0 hdim L
    (by rw [hd]; exact_mod_cast hpos)
  refine ⟨m₀, fun m hm => ?_⟩
  have h := finrank_cohomologyOverField_zero_sub_one_natTensorPow f h0 hg hdim L m
  have h1 : Module.finrank k (cohomologyOverField k f (natTensorPow L m) 1) = 0 :=
    have := ModuleCat.subsingleton_of_isZero (hm₀ m hm)
    Module.finrank_zero_of_subsingleton
  rw [h1, hd] at h
  push_cast at h
  zify
  linarith

/-- **`dim_k H⁰(X, ℒ^{⊗ m}) ≤ d · m` for every large `m`**, the upper half of
`exists_forall_finrank_cohomologyOverField_zero_natTensorPow_eq`. -/
theorem exists_forall_finrank_cohomologyOverField_zero_natTensorPow_le [IsProper f]
    [SmoothOfRelativeDimension 1 f] (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (hg : genus f = 1) (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] {d : ℕ} (hd : invertibleCurveDegree k f hdim L = d)
    (hpos : 0 < d) :
    ∃ m₀ : ℕ, ∀ m : ℕ, m₀ ≤ m →
      Module.finrank k (cohomologyOverField k f (natTensorPow L m) 0) ≤ d * m := by
  obtain ⟨m₀, hm₀⟩ :=
    exists_forall_finrank_cohomologyOverField_zero_natTensorPow_eq f h0 hg hdim L hd hpos
  exact ⟨m₀, fun m hm => (hm₀ m hm).le⟩

/-! ### The degree of a multiple of a rational point -/

/-- **An integral scheme universally closed over `k` with a `k`-rational point has
`Γ(Z, 𝒪_Z) = k`.** The ring of global functions is a field ([Stacks, Tag 04L2] (1)); the point
gives a ring map `Γ(Z, 𝒪_Z) ⟶ k` left inverse to the structure map, and a ring map out of a field
is injective, so the structure map is bijective. -/
theorem finrank_globalSections_eq_one_of_section {Z : Scheme.{u}} (g : Z ⟶ Spec (.of k))
    [IsIntegral Z] [UniversallyClosed g] (q : Spec (.of k) ⟶ Z) (hq : q ≫ g = 𝟙 _) :
    letI : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
    Module.finrank k Γ(Z, ⊤) = 1 := by
  let : Algebra k Γ(Z, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop).hom.toAlgebra
  let : Field Γ(Z, ⊤) := (isField_of_universallyClosed k g).toField
  let φ : Γ(Z, ⊤) →+* k := (q.appTop ≫ (Scheme.ΓSpecIso (.of k)).hom).hom
  have hcomp : (Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ q.appTop ≫
      (Scheme.ΓSpecIso (.of k)).hom = 𝟙 _ := by
    rw [← Category.assoc g.appTop, ← Scheme.Hom.comp_appTop, hq, Scheme.Hom.id_appTop,
      Category.id_comp, Iso.inv_hom_id]
  have hφ : ∀ c : k, φ (algebraMap k Γ(Z, ⊤) c) = c := fun c =>
    congrArg (fun h => h.hom c) hcomp
  have hbij : Function.Bijective (algebraMap k Γ(Z, ⊤)) :=
    ⟨(algebraMap k Γ(Z, ⊤)).injective, fun z => ⟨φ z, φ.injective (hφ (φ z))⟩⟩
  rw [← (AlgEquiv.ofBijective (Algebra.ofId k Γ(Z, ⊤)) hbij).toLinearEquiv.finrank_eq,
    Module.finrank_self]

/-- **The reduced point `x = p(Spec k)` has degree one**: `deg 𝒪_X(x) = dim_k Γ(x, 𝒪_x) = 1`,
the residue field at `x` being `k` because `p` is a section. -/
theorem divisorInvertibleDegree_vanishingIdeal_point [IsProper f] [SmoothOfRelativeDimension 1 f]
    (h0 : Module.finrank k (structureSheafCohomology f 0) = 1) (p : Spec (.of k) ⟶ X)
    (hp : p ≫ f = 𝟙 _) :
    divisorInvertibleDegree k f
      (Scheme.IdealSheafData.vanishingIdeal (⟨{point p}, isClosed_point f p hp⟩ : Closeds X)) =
      1 := by
  have := isCurve f h0
  have hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  set D := Scheme.IdealSheafData.vanishingIdeal (⟨{point p}, isClosed_point f p hp⟩ : Closeds X)
  have : IsEffectiveCartierDivisor D := isEffectiveCartierDivisor f h0 p hp
  have : IsIntegral D.subscheme := isIntegral_subscheme_vanishingIdeal (isClosed_point f p hp)
  have hrange : Set.range p = ({point p} : Set X) := by
    ext y
    constructor
    · rintro ⟨z, rfl⟩
      rw [Set.mem_singleton_iff]
      exact congrArg p (Subsingleton.elim _ _)
    · rintro rfl
      exact ⟨_, rfl⟩
  have hker : D.subschemeι.ker ≤ p.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.Hom.ker_eq_vanishingIdeal_closure_range]
    refine le_of_eq (congrArg Scheme.IdealSheafData.vanishingIdeal ?_)
    ext1
    rw [Closeds.coe_closure, hrange, (isClosed_point f p hp).closure_eq]
    rfl
  let q : Spec (.of k) ⟶ D.subscheme := IsClosedImmersion.lift D.subschemeι p hker
  have hq : q ≫ D.subschemeι ≫ f = 𝟙 _ := by
    rw [IsClosedImmersion.lift_fac_assoc, hp]
  have : IsFinite (D.subschemeι ≫ f) := isFinite_divisorSubscheme k f hdim D
  have key := curveDegree_invertibleSheaf_eq_finrank_globalSections k f hdim D
  rw [finrank_globalSections_eq_one_of_section (D.subschemeι ≫ f) q hq] at key
  rw [← invertibleCurveDegree_eq_divisorInvertibleDegree k f hdim D]
  have := isFiniteLocallyFreeOfRank_one_invertibleSheaf D
  rw [invertibleCurveDegree_eq_curveDegree]
  exact_mod_cast key

/-- The divisor of the empty ideal has degree zero: `𝒪_X(∅) ≅ 𝒪_X`. -/
theorem divisorInvertibleDegree_top :
    divisorInvertibleDegree k f (⊤ : X.IdealSheafData) = 0 := by
  have e : modulesInvertibleSheaf (⊤ : X.IdealSheafData) ≅
      SheafOfModules.unit X.ringCatSheaf := invertibleSheafTopIsoUnit
  unfold divisorInvertibleDegree
  rw [finsum_congr fun n => by rw [finrank_cohomologyOverField_eq_of_iso k f e n], sub_self]

/-- **The divisor `n · p` has degree `n`**, for every `n`: the degree is multiplicative in the
multiple ([Stacks, Tag 0AYX]) and the reduced point has degree one. -/
theorem divisorInvertibleDegree_vanishingIdeal_point_pow [IsProper f]
    [SmoothOfRelativeDimension 1 f] (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) (n : ℕ) :
    divisorInvertibleDegree k f
      (Scheme.IdealSheafData.vanishingIdeal (⟨{point p}, isClosed_point f p hp⟩ : Closeds X) ^ n) =
      n := by
  have := isCurve f h0
  have hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (f := f)).le
  cases n with
  | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top, divisorInvertibleDegree_top]; rfl
  | succ m =>
      rw [divisorInvertibleDegree_pow_succ k f hdim _ (isEffectiveCartierDivisor f h0 p hp) m,
        divisorInvertibleDegree_vanishingIdeal_point f h0 p hp]
      push_cast
      ring

/-- **The invertible module `𝒪_X(n · p)` has degree `n`.** -/
theorem invertibleCurveDegree_vanishingIdeal_point_pow [IsProper f]
    [SmoothOfRelativeDimension 1 f] (h0 : Module.finrank k (structureSheafCohomology f 0) = 1)
    (hdim : topologicalKrullDim X ≤ 1) (p : Spec (.of k) ⟶ X) (hp : p ≫ f = 𝟙 _) (n : ℕ)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (modulesInvertibleSheaf
      (Scheme.IdealSheafData.vanishingIdeal (⟨{point p}, isClosed_point f p hp⟩ : Closeds X) ^
        n))] :
    invertibleCurveDegree k f hdim (modulesInvertibleSheaf
      (Scheme.IdealSheafData.vanishingIdeal (⟨{point p}, isClosed_point f p hp⟩ : Closeds X) ^
        n)) = n :=
  (invertibleCurveDegree_eq_divisorInvertibleDegree k f hdim _).trans
    (divisorInvertibleDegree_vanishingIdeal_point_pow f h0 p hp n)

end AlgebraicGeometry.GenusOne

end
