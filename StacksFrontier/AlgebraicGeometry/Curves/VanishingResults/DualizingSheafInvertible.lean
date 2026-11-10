module

public import StacksFrontier.AlgebraicGeometry.AmpleCurve.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleDegreeCriterion.CurveInputs
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.AmpleRelativeFiniteType.VeryAmple
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Integral
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.PrescribedLowCohomologyFieldExtension
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafBaseChangeIso
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafCoherence
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingTwistGenerationCoherent
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SituationVeryAmpleGeneration
public import StacksFrontier.AlgebraicGeometry.Descent.OpenSubsetFpqc
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorSheafMap
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FreeNeighbourhood
public import StacksFrontier.AlgebraicGeometry.HQuasiProjectiveDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.ModuleDescent.InvertibleInput
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.PowerFamilyBridge.Ample
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundleProperFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.PullbackDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.VeryAmpleVanishAtClosedPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal
public import StacksFrontier.AlgebraicGeometry.VeryAmpleAffineBase.FiniteGlobalSections
public import StacksFrontier.RingTheory.DiscreteValuationRing.FreeOfInjectiveEndomorphism
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing sheaf of a normal curve over an algebraically closed field is invertible

Let `k` be an algebraically closed field and `X` a normal proper curve over `k`. This file proves
that the dualizing sheaf `ω_X = H^{-1}(f^×(𝒪_{Spec k}))` of [Stacks, Tag 0BS2] is an invertible
`𝒪_X`-module. (For a smooth proper curve over any field the invertibility of `ω_X` is
`AlgebraicGeometry.isInvertible_dualizingSheafOverField_of_isCurve`.)

## Main results

All in the namespace `AlgebraicGeometry`:

* `CohenMacaulayCurveSituation.exists_isRelativelyVeryAmple_two_le_invertibleCurveDegree`:
  a proper curve over a field carries a very ample invertible module of degree at least two.
* `CohenMacaulayCurveSituation.free_modulesStalk_dualizingSheafOverField_of_isClosed`:
  over an algebraically closed field, the stalk of `ω_X` at a closed point of a normal curve is
  free.
* `CohenMacaulayCurveSituation.stalkLengthNat_genericPoint_dualizingSheafOverField`:
  `ω_X` has length one at the generic point of an integral curve over an algebraically closed
  field.
* `CohenMacaulayCurveSituation.isInvertible_dualizingSheafOverField_of_isAlgClosed`:
  `ω_X` is invertible for a normal curve over an algebraically closed field.
* `cohenMacaulayCurveSituationOfIsCurve`: the datum of Situation
  [Stacks, Tag 0B5D] attached to a proper curve over `k` with `H⁰(X, 𝒪_X) = k`.

## The argument

Everything rests on the two consequences of duality already available for `ω_X`: clause (5) of
[Stacks, Tag 0BS2], `Hom(ℱ, ω_X) = H¹(X, ℱ)^∨`, and the Cohen--Macaulay assertion of clause (2)
derived from it (`ω_X` has no nonzero coherent submodule supported in dimension zero). The local
theory of dualizing complexes ([Stacks, Tags 0AU3, 0AWN]) is not used.

* **Coherence** is `isCoherent_dualizingSheafOverField_of_generatingSections`, for a very ample
  module of degree at least two, which exists on any proper curve ([Stacks, Tags 0A26, 01VT]).
* **Freeness at a closed point `x`.** For a section `s` of a very ample `ℒ` vanishing at `x` and
  at no generic point ([Stacks, Tag 0B58]), multiplication by `s` is injective on `ω_X`, because
  its kernel is supported in dimension zero; at `x` it lands in `𝔪_x (ω ⊗ ℒ)_x`, and a section
  not vanishing at `x` identifies `(ω ⊗ ℒ)_x` with `ω_{X,x}`. So `ω_{X,x}` has an injective
  endomorphism into `𝔪_x ω_{X,x}`, and over the discrete valuation ring `𝒪_{X,x}` this forces
  freeness (`IsDiscreteValuationRing.free_of_injective_of_range_le_maximalIdeal_smul`).
* **Rank one.** Along a globally generated `ℒ` of degree at least two, the degree of `ω_X` is
  `length_η(ω_X) · deg ℒ` and, by clause (5), at most `deg ℒ`.

No Stacks attribute is attached: the statement is a special case of [Stacks, Tag 0C19], which
is stated in the source for Gorenstein curves.

## References

* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0C19](https://stacks.math.columbia.edu/tag/0C19)
* [Stacks Project, Tag 0B58](https://stacks.math.columbia.edu/tag/0B58)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CohenMacaulayCurveSituation

variable (S : CohenMacaulayCurveSituation.{u})

/-- `deg(L^{⊗ n}) = n deg(L)` for the tensor powers `Stacks.Ample.tensorPowModule`. -/
theorem invertibleCurveDegree_tensorPowModule_natCast (L : S.X.Modules)
    [Stacks.Ample.IsInvertibleModule S.X L] (n : ℕ) :
    invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one)
        (Stacks.Ample.tensorPowModule S.X L (n : ℤ)) =
      (n : ℤ) * invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    exact invertibleCurveDegree_eq_zero_of_iso_unit S.k S.f _ _
      (Stacks.Ample.tensorPowModuleZeroIso S.X L)
  | succ n ih =>
    have e := Stacks.Ample.tensorPowModuleAddIso S.X L (n : ℤ) 1
    have h1 := invertibleCurveDegree_eq_of_iso S.k S.f (le_of_eq S.dimension_one) e
    have h2 := invertibleCurveDegree_tensorSheaf_eq_add S.k S.f (le_of_eq S.dimension_one)
      (Stacks.Ample.tensorPowModule S.X L (n : ℤ)) (Stacks.Ample.tensorPowModule S.X L 1)
    have h3 := invertibleCurveDegree_eq_of_iso S.k S.f (le_of_eq S.dimension_one)
      (Stacks.Ample.tensorPowModuleOneIso S.X L)
    push_cast
    rw [← h1, h2, ih, h3]
    ring

/-- **A proper curve over a field carries a very ample invertible module of degree at least
two.** The curve is projective ([Stacks, Tag 0A26]), so it carries a very ample `ℒ`, which is
ample ([Stacks, Tag 01VT]); every high power of `ℒ` is very ample, and its degree is a multiple
of the positive degree of `ℒ`. -/
theorem exists_isRelativelyVeryAmple_two_le_invertibleCurveDegree [IsCurve S.k S.f] :
    ∃ (L : S.X.Modules) (_ : Stacks.Ample.IsInvertibleModule S.X L),
      Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L ∧
        2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L := by
  open Stacks.HQuasiProjectiveDimensionOne in
  have hproj : IsProjective S.f :=
    (isProjectiveMorphism_of_isProper_of_topologicalKrullDim_le_one
      S.f (le_of_eq S.dimension_one)).isProjective
  obtain ⟨L, hL, hva⟩ := hproj.exists_isRelativelyVeryAmple
  have hva1 : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f
      (Stacks.Ample.tensorPowModule S.X L ((1 : ℕ) : ℤ)) :=
    Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple.of_iso
      (Stacks.Ample.tensorPowModuleOneIso S.X L).symm hva
  have hamp : Stacks.Ample.IsAmple S.X L :=
    (Stacks.AmpleRelativeFiniteType.isAmple_iff_exists_isRelativelyVeryAmple S.f L).2
      ⟨1, le_rfl, hva1⟩
  obtain ⟨d₀, hd₀, hall⟩ :=
    (Stacks.AmpleRelativeFiniteType.isAmple_iff_eventually_isRelativelyVeryAmple S.f L).1 hamp
  have hpos : 0 < invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L := by
    have hmod : Scheme.Modules.IsAmple S.X L :=
      Stacks.PowerFamilyBridge.modulesIsAmple_of_isAmple S.X L hamp
    exact invertibleCurveDegree_pos_of_isAmple_of_isCurve S.k S.f _ L hmod
  refine ⟨Stacks.Ample.tensorPowModule S.X L ((2 * d₀ : ℕ) : ℤ), inferInstance,
    hall _ (by omega), ?_⟩
  rw [invertibleCurveDegree_tensorPowModule_natCast]
  push_cast
  nlinarith

open Stacks.ModuleSkyscraper (modulesStalkFunctor) in
/-- **Multiplication by a section of `ℒ` vanishing at `x` only at closed points is injective on
`ω_X`.** Its kernel is coherent and unsupported at every generic point, hence supported in
dimension zero, and `ω_X` has no such nonzero submodule (clause (2) of [Stacks, Tag 0BS2]). -/
theorem mono_sectionMulHom_dualizingSheafOverField
    (hωc : (Stacks.Duality.dualizingSheafOverField S.f).IsCoherent) (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L] (s : Γ(L, ⊤)) {x : S.X}
    (hx : IsClosed ({x} : Set S.X))
    (hgen : ∀ Z ∈ irreducibleComponents S.X, ∀ y, IsGenericPoint y Z → y ≠ x →
      y ∈ Stacks.Ample.nonvanishingLocus L s) :
    Mono (sectionMulHom (Stacks.Duality.dualizingSheafOverField S.f) L s) := by
  set ω := Stacks.Duality.dualizingSheafOverField S.f
  have hdim1 : topologicalKrullDim (S.X : Type u) ≤ 1 := le_of_eq S.dimension_one
  have hgenAll : ∀ y ∈ Stacks.AlgebraicGeometry.ComponentDegrees.genericPointsOne S.X,
      y ∈ Stacks.Ample.nonvanishingLocus L s :=
    fun y hy => mem_nonvanishingLocus_of_mem_genericPointsOne L s hx hgen hy
  have hLc := S.isCoherent_of_isInvertible' L
  have := hωc
  have : ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨S.X.presheaf,
      Presheaf.isSheaf_of_isSheaf_comp _ (S.X.presheaf) (forget₂ CommRingCat RingCat)
      (S.X.ringCatSheaf.property)⟩).obj ω).obj L)).IsCoherent :=
    S.isCoherent_tensorSheaf' ω L hωc hLc
  have hkercoh : (kernel (sectionMulHom ω L s)).IsCoherent :=
    isCoherent_kernel_of_isCoherent ‹ω.IsCoherent› ‹_› (sectionMulHom ω L s)
  have hkerdim : topologicalKrullDim
      (SheafOfModules.supp (kernel (sectionMulHom ω L s))) ≤ 0 :=
    topologicalKrullDim_supp_le_zero_of_forall_notMem_genericPointsOne hdim1 _ hkercoh
      fun y hy => notMem_supp_kernel_of_injective_mapFun _ y
        (bijective_mapFun_sectionMulHom ω L s (hgenAll y hy)).1
  have hmonoι : Mono (kernel.ι (sectionMulHom ω L s)) :=
    ⟨fun _ _ h => Fork.IsLimit.hom_ext (kernelIsKernel (sectionMulHom ω L s)) h⟩
  have hkerzero : IsZero (kernel (sectionMulHom ω L s)) :=
    S.noCoherentSubmoduleOfZeroDimensionalSupport_dualizingSheafOverField _
      (kernel.ι (sectionMulHom ω L s)) hmonoι hkercoh hkerdim
  exact (Preadditive.mono_iff_isZero_kernel _).mpr hkerzero

open Stacks.ModuleSkyscraper (modulesStalkFunctor) in
/-- **The stalk of `ω_X` at a closed point of a normal curve over an algebraically closed field
is free.** Pick a very ample `ℒ`, a global section `s` vanishing at `x` but at no generic point
([Stacks, Tag 0B58]) and a global section `s'` not vanishing at `x`. Multiplication by `s` is
injective on `ω_X` (`mono_sectionMulHom_dualizingSheafOverField`) and lands in `𝔪_x (ω ⊗ ℒ)_x`
at `x`, while multiplication by `s'` identifies `ω_{X,x}` with `(ω ⊗ ℒ)_x`. So `ω_{X,x}` carries
an injective endomorphism into `𝔪_x ω_{X,x}`, and the local ring at `x` is a discrete valuation
ring; such a module is free
(`IsDiscreteValuationRing.free_of_injective_of_range_le_maximalIdeal_smul`). -/
theorem free_modulesStalk_dualizingSheafOverField_of_isClosed [IsAlgClosed S.k]
    [IsCurve S.k S.f] [IsNormal S.X]
    (hωc : (Stacks.Duality.dualizingSheafOverField S.f).IsCoherent) (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L) (x : S.X)
    (hx : IsClosed ({x} : Set S.X)) :
    Module.Free (S.X.presheaf.stalk x)
      ((modulesStalkFunctor S.X x).obj (Stacks.Duality.dualizingSheafOverField S.f)) := by
  set ω := Stacks.Duality.dualizingSheafOverField S.f
  have : IsNoetherian S.X := S.isNoetherian
  obtain ⟨s, hsx, hgen⟩ :=
    exists_globalSection_vanishing_at_isClosed_nonvanishing_genericPoint S.f L hL x hx
  obtain ⟨s', hs'⟩ := S.exists_mem_nonvanishingLocus L hL x
  have := S.mono_sectionMulHom_dualizingSheafOverField hωc L s hx hgen
  have hz : IsZero (kernel (sectionMulHom ω L s)) :=
    (Preadditive.mono_iff_isZero_kernel _).mp inferInstance
  have : Mono ((modulesStalkFunctor S.X x).map (sectionMulHom ω L s)) :=
    (Preadditive.mono_iff_isZero_kernel _).mpr
      (((modulesStalkFunctor S.X x).map_isZero hz).of_iso
        (PreservesKernel.iso (modulesStalkFunctor S.X x) (sectionMulHom ω L s)).symm)
  have hinj : Function.Injective ((modulesStalkFunctor S.X x).map (sectionMulHom ω L s)).hom :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hbij : Function.Bijective
      ((modulesStalkFunctor S.X x).map (sectionMulHom ω L s')).hom :=
    bijective_mapFun_sectionMulHom ω L s' hs'
  let e := LinearEquiv.ofBijective _ hbij
  let φ := e.symm.toLinearMap ∘ₗ ((modulesStalkFunctor S.X x).map (sectionMulHom ω L s)).hom
  have hφinj : Function.Injective φ := e.symm.injective.comp hinj
  have hφrange : LinearMap.range φ ≤
      IsLocalRing.maximalIdeal (S.X.presheaf.stalk x) • ⊤ := by
    rw [LinearMap.range_comp]
    refine (Submodule.map_mono (range_modulesStalkFunctor_map_sectionMulHom_le ω L s hsx)).trans ?_
    rw [Submodule.map_smul'', Submodule.map_top, LinearEquiv.range]
  have : IsIntegrallyClosed (S.X.presheaf.stalk x) := IsNormal.stalk_normal x
  have : IsDiscreteValuationRing (S.X.presheaf.stalk x) :=
    ((isDiscreteValuationRing_stalk_tfae_of_isCurve S.k S.f hx).out 2 3).mp
      (IsNormalRing.of_isIntegrallyClosed _)
  have : Module.Finite (S.X.presheaf.stalk x) ((modulesStalkFunctor S.X x).obj ω) :=
    Scheme.Modules.finite_stalk_of_isCoherent ω x
  exact IsDiscreteValuationRing.free_of_injective_of_range_le_maximalIdeal_smul φ hφinj hφrange

open Stacks.AlgebraicGeometry.ComponentDegrees in
open Stacks.AlgebraicGeometry.ComponentDegreeDevissage in
/-- **`ω_X` has length one at the generic point of an integral curve over an algebraically
closed field.** For a globally generated very ample `ℒ` of degree at least two, the degree of
`ω_X` along `ℒ` is `length_η(ω_X) · deg ℒ` (the one-term sum of [Stacks, Tag 0AYW]) and is at
most `deg ℒ` (`twistDegree_le_of_mono`, a consequence of clause (5) of [Stacks, Tag 0BS2]); so the
length is at most one. It is not zero, for then `ω_X` would be supported in dimension zero and
hence vanish by the Cohen--Macaulay assertion of clause (2) of [Stacks, Tag 0BS2]. -/
theorem stalkLengthNat_genericPoint_dualizingSheafOverField [IsAlgClosed S.k] [IsIntegral S.X]
    (hωc : (Stacks.Duality.dualizingSheafOverField S.f).IsCoherent) (L : S.X.Modules)
    [SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2 L]
    (hL : Stacks.Tag01VMVeryAmple.IsRelativelyVeryAmple S.f L) (σ : L.GeneratingSections)
    (hd : 2 ≤ invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L) :
    stalkLengthNat (Stacks.Duality.dualizingSheafOverField S.f) (genericPoint S.X) = 1 := by
  classical
  set ω := Stacks.Duality.dualizingSheafOverField S.f
  have : IsNoetherian S.X := S.isNoetherian
  have : Fintype (genericPointsOne S.X) :=
    @Fintype.ofFinite _ (finite_genericPointsOne S.X).to_subtype
  let ξ : genericPointsOne S.X :=
    ⟨genericPoint S.X, genericPoint_self_mem_genericPointsOne S.X S.dimension_one⟩
  have huniq : ∀ η : genericPointsOne S.X, η = ξ :=
    fun η => Subtype.ext (eq_genericPoint_of_mem_genericPointsOne S.X S.dimension_one η)
  have hsum : ∀ g : genericPointsOne S.X → ℤ, ∑ η, g η = g ξ := fun g =>
    Fintype.sum_eq_single ξ fun η hη => absurd (huniq η) hη
  have hcd : invertibleCurveDegree S.k S.f (le_of_eq S.dimension_one) L =
      componentDegree S.k S.f (le_of_eq S.dimension_one) L 1 ξ := by
    rw [invertibleCurveDegree_eq_curveDegree,
      curveDegree_eq_finsum_componentDegree_of_isIntegral S.k S.f _ S.dimension_one L 1,
      finsum_componentDegree_of_isIntegral S.X S.dimension_one]
  have hpos := S.componentDegree_pos_of_isRelativelyVeryAmple L hL ξ
  have hle := S.twistDegree_le_of_mono L σ hd ω hωc (𝟙 ω)
  rw [twistDegree_eq_sum, hsum, hcd] at hle
  have hle1 : stalkLengthNat ω (genericPoint S.X) ≤ 1 := by
    by_contra h
    push Not at h
    have : (2 : ℤ) ≤ (stalkLengthNat ω (genericPoint S.X) : ℤ) := by exact_mod_cast h
    nlinarith
  have hne : stalkLengthNat ω (genericPoint S.X) ≠ 0 := by
    intro h0
    have htw : S.twistDegree L ω hωc = 0 := by
      rw [twistDegree_eq_sum, hsum]
      change (stalkLengthNat ω (genericPoint S.X) : ℤ) * _ = 0
      rw [h0]
      simp
    have hsupp := S.supp_dim_le_zero_of_twistDegree_eq_zero hL ω hωc htw
    exact S.not_isZero_dualizingSheafOverField
      (S.noCoherentSubmoduleOfZeroDimensionalSupport_dualizingSheafOverField ω (𝟙 ω)
        inferInstance hωc hsupp)
  omega

open Stacks.ModuleSkyscraper (modulesStalkFunctor) in
/-- **The dualizing sheaf of a normal proper curve over an algebraically closed field with
`H⁰(X, 𝒪_X) = k` is invertible.** It is coherent (`isCoherent_dualizingSheafOverField_of_
generatingSections`, for a very ample `ℒ` of degree at least two), its stalks at closed points
are free (`free_modulesStalk_dualizingSheafOverField_of_isClosed`) and its stalk at the generic
point is a vector space over the function field, so it is finite locally free; its rank at the
generic point is one (`stalkLengthNat_genericPoint_dualizingSheafOverField`), hence everywhere,
the scheme being integral. -/
theorem isInvertible_dualizingSheafOverField_of_isAlgClosed [IsAlgClosed S.k] [IsCurve S.k S.f]
    [IsNormal S.X] :
    SheafOfModules.IsInvertible S.X.presheaf S.X.ringCatSheaf.2
      (Stacks.Duality.dualizingSheafOverField S.f) := by
  set ω := Stacks.Duality.dualizingSheafOverField S.f
  obtain ⟨L, hLinv, hL, hd⟩ := S.exists_isRelativelyVeryAmple_two_le_invertibleCurveDegree
  obtain ⟨σ⟩ := S.nonempty_generatingSections_of_isRelativelyVeryAmple L hL
  have hωc : ω.IsCoherent := S.isCoherent_dualizingSheafOverField_of_generatingSections L hL σ hd
  have : IsLocallyNoetherian S.X := LocallyOfFiniteType.isLocallyNoetherian S.f
  have hfield : IsField (S.X.presheaf.stalk (genericPoint S.X)) :=
    Field.toIsField S.X.functionField
  have hfree : ∀ x : S.X, Module.Free (S.X.presheaf.stalk x)
      ((modulesStalkFunctor S.X x).obj ω) := by
    intro x
    by_cases hx : x = genericPoint S.X
    · subst hx
      let : Field (S.X.presheaf.stalk (genericPoint S.X)) := hfield.toField
      exact Module.Free.of_divisionRing _ _
    · exact S.free_modulesStalk_dualizingSheafOverField_of_isClosed hωc L hL x
        (Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint S.X
          S.dimension_one hx)
  have hflf : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} ω :=
    (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators ω).mp
      (Scheme.Modules.isFiniteLocallyFree_of_forall_free_stalk ω hωc hfree)
  have hrank : Scheme.Modules.fiberRank ω (genericPoint S.X) = 1 := by
    rw [fiberRank_eq_finrank_stalk_of_isField ω _ hfield]
    have h1 := S.stalkLengthNat_genericPoint_dualizingSheafOverField hωc L hL σ hd
    let : Field (S.X.presheaf.stalk (genericPoint S.X)) := hfield.toField
    have : Module.Finite (S.X.presheaf.stalk (genericPoint S.X))
        (ω.presheaf.stalk (genericPoint S.X)) :=
      Scheme.Modules.finite_stalk_of_isCoherent ω _
    unfold Stacks.AlgebraicGeometry.ComponentDegreeDevissage.stalkLengthNat at h1
    rw [Module.length_eq_finrank] at h1
    exact_mod_cast h1
  have := Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq ω 1 _ hrank
  exact Stacks.ModuleDescent.isInvertible_of_isFiniteLocallyFreeOfRank_one S.X ω this

end AlgebraicGeometry.CohenMacaulayCurveSituation

namespace AlgebraicGeometry

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The datum of Situation [Stacks, Tag 0B5D] attached to a proper curve over `k` with
`H⁰(X, 𝒪_X) = k`. -/
abbrev cohenMacaulayCurveSituationOfIsCurve [IsCurve k f] [IsProper f]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)] : CohenMacaulayCurveSituation.{u} where
  k := k
  X := X
  f := f
  dimension_one := IsCurve.topologicalKrullDim_eq_one (k := k) (f := f)

end AlgebraicGeometry
