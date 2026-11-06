module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DiscreteValuationStalkAffine
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreMaximalPrime
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreReplacement
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ReducedFibreSolution
public import StacksFrontier.RingTheory.DiscreteValuationRing.IntegralClosureCompositumBase
public import StacksFrontier.RingTheory.DiscreteValuationRing.SolutionCanonical
public import StacksFrontier.RingTheory.FormallySmooth.IntegralClosureBaseLocalization

/-!
# Smoothness of the normalized base change at a point over a solved bad point

Let `R` be a Nagata Dedekind domain with fraction field `K`, let `g : Y ⟶ Spec R` be flat,
quasi-compact and locally of finite type with `Y` normal, let `K₁ / K` be finite and let
`B = integralClosure R K₁`.  Let `y` be a point of the normalization `Y₁` of
`Y ×_{Spec R} Spec B` which is a generic point of an irreducible component of its own fibre over
`Spec B`, that fibre not the generic one, and let `x` be the point of `Y` below it.  **If `K₁` is
a solution for the extension of discrete valuation rings `R_x → 𝒪_{Y, x}`, then `Y₁ ⟶ Spec B` is
smooth at `y`.**

This is the second half of the last paragraph of the proof of the reduced fibre theorem: the
points of the normalized base change lying *outside* the smooth locus, which the elimination of
ramification has to reach.

Four things are composed.  The local ring `𝒪_{Y₁, y}` is a localization at a maximal ideal `q` of
the integral closure `T` of `𝒪_{Y, x}` in the reduction of `R(Y) ⊗_K K₁`
(`Scheme.exists_isMaximal_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ`),
by an isomorphism carrying the germ of a section of `B` to its image in `T`.  That ring `T` is
the `B₁` of `IsDiscreteValuationRing.canonicalBaseChange`, onto which the solution property of
the package produced by `AlgebraicGeometry.IsSolutionForStalk` transports
(`IsDiscreteValuationRing.IntegralClosureBaseChange.isSolution_canonicalBaseChange`); its `A₁` is
`integralClosure R_x K₁`, a localization of `B`, across which adic formal smoothness descends
(`RingHom.formallySmoothNAdic_localRingHom_integralClosure_primeCompl`) — and the two `B`-algebra
structures on `T` that the two readings use agree, by
`algebraMap_integralClosureCompositumOfBase_eq`.  The resulting adically formally smooth
localization `B_{q ∩ B} → T_q` feeds
`AlgebraicGeometry.smoothAt_of_formallySmoothNAdic_localizationAtPrime_germ`.

## Main results

* `AlgebraicGeometry.algebraStalkOfBase` and `AlgebraicGeometry.isScalarTower_algebraStalkOfBase`,
  `AlgebraicGeometry.isScalarTower_algebraStalkFractionRing`: the `R`-algebra structure on the
  local ring at `x` given by the germ, and the two towers it sits in.
* `AlgebraicGeometry.isDomain_stalk_spec`,
  `AlgebraicGeometry.isDiscreteValuationRing_stalk_spec`: the local ring of `Spec B` at a nonzero
  prime of a Dedekind domain is a discrete valuation ring.
* `AlgebraicGeometry.formallySmoothNAdic_localRingHom_of_isSolutionForStalk`: the solution
  property read over the unlocalized base `B`.
* `AlgebraicGeometry.smoothAt_normalization_pullback_of_isSolutionForStalk`: the smoothness.

## Implementation notes

The point `x` is not an argument: it is `pr₁ (ν y)`, and the hypotheses `hs`, `hg`, `hsol` are
stated at that point.  The bad-point conditions on `x` are *not* derived here from the conditions
on `y`; that derivation is going down for the integral morphism `ν ≫ pr₁`
(`AlgebraicGeometry.mem_genericPoints_asFiber_normalization_pullbackFst`) together with the
comparison of the fibres over `Spec B` and over `Spec R`
(`AlgebraicGeometry.mem_genericPoints_asFiber_comp_of_isIntegralHom`), and it belongs to the
assembly rather than here.

`AlgebraicGeometry.IsSolutionForStalk` is `@[expose]` so that the package it asserts to exist can
be destructured outside its own module; nothing else about it changed.

## References

* [Stacks Project, Tag 09IL](https://stacks.math.columbia.edu/tag/09IL)
* [Stacks Project, Tag 09EM](https://stacks.math.columbia.edu/tag/09EM)
* [Stacks Project, Tag 09EN](https://stacks.math.columbia.edu/tag/09EN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

open scoped TensorProduct

universe u

attribute [local instance] Algebra.TensorProduct.rightAlgebra
  IsDiscreteValuationRing.isScalarTower_tensor_of_base
  IsDiscreteValuationRing.algebraIntegralClosure

namespace AlgebraicGeometry

section Plumbing

variable {R : Type u} [CommRing R] (K : Type u) [Field K] [Algebra R K]
  {Y : Scheme.{u}} (g : Y ⟶ Spec (.of R)) (x : Y)

/-- The local ring of `Y` at `x` is an `R`-algebra through the germ at `x` of the structure
map of `R`. -/
@[instance_reducible]
def algebraStalkOfBase : Algebra R (Y.presheaf.stalk x) :=
  ((Scheme.ΓSpecIso (.of R)).inv ≫ g.appTop ≫ Y.presheaf.germ ⊤ x trivial).hom.toAlgebra

/-- The germ of the structure map of `R` factors through the localization of `R` at the prime
under `x`. -/
theorem isScalarTower_algebraStalkOfBase :
    letI : (g.base x).asIdeal.IsPrime := (g.base x).isPrime
    letI := algebraStalkOfBase g x
    letI := stalkAlgebraOfSpecHom g x
    IsScalarTower R (Localization.AtPrime (g.base x).asIdeal) (Y.presheaf.stalk x) :=
  let : (g.base x).asIdeal.IsPrime := (g.base x).isPrime
  let := algebraStalkOfBase g x
  let := stalkAlgebraOfSpecHom g x
  IsScalarTower.of_algebraMap_eq fun r ↦
    DFunLike.congr_fun (CommRingCat.hom_ext_iff.mp (germ_structureMap_eq g x)) r

variable [IsDedekindDomain R] [IsFractionRing R K] [Flat g] [LocallyOfFiniteType g] [IsNormal Y]

omit [LocallyOfFiniteType g] in
/-- The structure map `R → Frac 𝒪_{Y, x}` factors through `K`. -/
theorem isScalarTower_algebraStalkFractionRing :
    letI : (g.base x).asIdeal.IsPrime := (g.base x).isPrime
    letI := algebraStalkOfBase g x
    letI := algebraStalkFractionRing K g x
    IsScalarTower R K (FractionRing (Y.presheaf.stalk x)) := by
  let : (g.base x).asIdeal.IsPrime := (g.base x).isPrime
  let := algebraStalkOfBase g x
  let := stalkAlgebraOfSpecHom g x
  let := algebraLocalizationAtPrimeBase K g x
  let := algebraStalkFractionRing K g x
  have := isScalarTower_algebraStalkOfBase g x
  have := isScalarTower_localizationAtPrimeBase K g x
  have := isScalarTower_stalkFractionRing K g x
  refine IsScalarTower.of_algebraMap_eq fun r ↦ ?_
  rw [IsScalarTower.algebraMap_apply R (Y.presheaf.stalk x) (FractionRing (Y.presheaf.stalk x)),
    IsScalarTower.algebraMap_apply R (Localization.AtPrime (g.base x).asIdeal)
      (Y.presheaf.stalk x),
    ← IsScalarTower.algebraMap_apply (Localization.AtPrime (g.base x).asIdeal)
      (Y.presheaf.stalk x) (FractionRing (Y.presheaf.stalk x)),
    IsScalarTower.algebraMap_apply (Localization.AtPrime (g.base x).asIdeal) K
      (FractionRing (Y.presheaf.stalk x)),
    ← IsScalarTower.algebraMap_apply R (Localization.AtPrime (g.base x).asIdeal) K]


variable (K₁ : Type u) [Field K₁] [Algebra K K₁] [Algebra R K₁] [IsScalarTower R K K₁]
  [Module.Finite K K₁] [Module.Finite R ↥(integralClosure R K₁)]

set_option synthInstance.maxHeartbeats 200000 in
/-- **The solution property, read over the unlocalized base.**  At a bad point `x` of `Y` for
which `K₁` is a solution, every maximal ideal `q` of the integral closure of `𝒪_{Y, x}` in the
reduced compositum has `(integralClosure R K₁)_{q ∩ -} → T_q` formally smooth for the
maximal-ideal-adic topology. -/
theorem formallySmoothNAdic_localRingHom_of_isSolutionForStalk
    (hs : (g.base x).asIdeal ≠ ⊥)
    (hg : g.asFiber x ∈ genericPoints ↥(g.fiber (g.base x)))
    (hsol : IsSolutionForStalk K g x hs hg K₁) :
    letI : (g.base x).asIdeal.IsPrime := (g.base x).isPrime
    letI := algebraStalkOfBase g x
    letI := algebraStalkFractionRing K g x
    haveI := isScalarTower_algebraStalkFractionRing K g x
    letI := algebraIntegralClosureCompositumOfBase R (Y.presheaf.stalk x) K
      (FractionRing (Y.presheaf.stalk x)) K₁
    ∀ q : Ideal ↥(integralClosure (Y.presheaf.stalk x)
        ((FractionRing (Y.presheaf.stalk x) ⊗[K] K₁) ⧸
          _root_.nilradical (FractionRing (Y.presheaf.stalk x) ⊗[K] K₁))),
      ∀ hq : q.IsMaximal,
      haveI : q.IsPrime := hq.isPrime
      haveI : (q.comap (algebraMap ↥(integralClosure R K₁)
        ↥(integralClosure (Y.presheaf.stalk x)
          ((FractionRing (Y.presheaf.stalk x) ⊗[K] K₁) ⧸
            _root_.nilradical (FractionRing (Y.presheaf.stalk x) ⊗[K] K₁))))).IsPrime :=
        Ideal.IsPrime.comap _
      RingHom.FormallySmoothNAdic.{u, u, u}
        (Localization.localRingHom (q.comap (algebraMap ↥(integralClosure R K₁)
            ↥(integralClosure (Y.presheaf.stalk x)
              ((FractionRing (Y.presheaf.stalk x) ⊗[K] K₁) ⧸
                _root_.nilradical (FractionRing (Y.presheaf.stalk x) ⊗[K] K₁))))) q
          (algebraMap ↥(integralClosure R K₁)
            ↥(integralClosure (Y.presheaf.stalk x)
              ((FractionRing (Y.presheaf.stalk x) ⊗[K] K₁) ⧸
                _root_.nilradical (FractionRing (Y.presheaf.stalk x) ⊗[K] K₁)))) rfl)
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) := by
  let : (g.base x).asIdeal.IsPrime := (g.base x).isPrime
  let := algebraStalkOfBase g x
  let := stalkAlgebraOfSpecHom g x
  let := algebraLocalizationAtPrimeBase K g x
  let := algebraStalkFractionRing K g x
  have := isScalarTower_algebraStalkOfBase g x
  have := isScalarTower_localizationAtPrimeBase K g x
  have := isScalarTower_stalkFractionRing K g x
  have := isScalarTower_algebraStalkFractionRing K g x
  have := isFractionRing_localizationAtPrimeBase K g x
  have := isDiscreteValuationRing_localizationAtPrimeBase g x hs
  have := isDiscreteValuationRing_stalk_of_mem_genericPoints g x hs hg
  have := isExtension_stalkAlgebraOfSpecHom g x
  let : Algebra (Localization.AtPrime (g.base x).asIdeal) K₁ :=
    ((algebraMap K K₁).comp
      (algebraMap (Localization.AtPrime (g.base x).asIdeal) K)).toAlgebra
  have : IsScalarTower (Localization.AtPrime (g.base x).asIdeal) K K₁ :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : IsScalarTower R (Localization.AtPrime (g.base x).asIdeal) K₁ :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R K K₁,
        IsScalarTower.algebraMap_apply (Localization.AtPrime (g.base x).asIdeal) K K₁,
        ← IsScalarTower.algebraMap_apply R (Localization.AtPrime (g.base x).asIdeal) K]
  let := algebraIntegralClosureOfLocalizedBase R (Localization.AtPrime (g.base x).asIdeal) K₁
  have := isScalarTower_integralClosureOfLocalizedBase_right R
    (Localization.AtPrime (g.base x).asIdeal) K₁
  have := isScalarTower_integralClosureOfLocalizedBase_left R
    (Localization.AtPrime (g.base x).asIdeal) K₁
  let := algebraIntegralClosureCompositumOfBase R (Y.presheaf.stalk x) K
    (FractionRing (Y.presheaf.stalk x)) K₁
  let : Algebra ↥(integralClosure (Localization.AtPrime (g.base x).asIdeal) K₁)
      ↥(integralClosure (Y.presheaf.stalk x)
        ((FractionRing (Y.presheaf.stalk x) ⊗[K] K₁) ⧸
          _root_.nilradical (FractionRing (Y.presheaf.stalk x) ⊗[K] K₁))) :=
    IsDiscreteValuationRing.algebraIntegralClosure
      (Localization.AtPrime (g.base x).asIdeal) (Y.presheaf.stalk x) K
      (FractionRing (Y.presheaf.stalk x)) K₁
  have : IsScalarTower ↥(integralClosure R K₁)
      ↥(integralClosure (Localization.AtPrime (g.base x).asIdeal) K₁)
      ↥(integralClosure (Y.presheaf.stalk x)
        ((FractionRing (Y.presheaf.stalk x) ⊗[K] K₁) ⧸
          _root_.nilradical (FractionRing (Y.presheaf.stalk x) ⊗[K] K₁))) :=
    isScalarTower_integralClosureCompositumOfBase R
      (Localization.AtPrime (g.base x).asIdeal) (Y.presheaf.stalk x) K
      (FractionRing (Y.presheaf.stalk x)) K₁
  intro q hq
  obtain ⟨D, hD⟩ := hsol
  have : q.IsPrime := hq.isPrime
  have hcanq : RingHom.FormallySmoothNAdic.{u, u, u}
      (Localization.localRingHom
        (q.comap (algebraMap
          ↥(integralClosure (Localization.AtPrime (g.base x).asIdeal) K₁) _)) q
        (algebraMap ↥(integralClosure (Localization.AtPrime (g.base x).asIdeal) K₁) _) rfl)
      (IsLocalRing.maximalIdeal (Localization.AtPrime q)) :=
    D.isSolution_canonicalBaseChange hD q hq
  exact RingHom.formallySmoothNAdic_localRingHom_integralClosure_primeCompl K
    (A := R) (A' := Localization.AtPrime (g.base x).asIdeal) (g.base x).asIdeal q hcanq



/-- The local ring of the spectrum of a domain at a point is a domain. -/
theorem isDomain_stalk_spec {B : Type u} [CommRing B] [IsDomain B] (b : Spec (.of B)) :
    IsDomain ((Spec (.of B)).presheaf.stalk b) :=
  let : b.asIdeal.IsPrime := b.isPrime
  Function.Injective.isDomain
    ((Spec.stalkIso (.of B) b).commRingCatIsoToRingEquiv : _ →+* Localization.AtPrime b.asIdeal)
    (Spec.stalkIso (.of B) b).commRingCatIsoToRingEquiv.injective

/-- The local ring of the spectrum of a Dedekind domain at a nonzero prime is a discrete
valuation ring. -/
theorem isDiscreteValuationRing_stalk_spec {B : Type u} [CommRing B] [IsDedekindDomain B]
    (b : Spec (.of B)) (hb : b.asIdeal ≠ ⊥) :
    letI := isDomain_stalk_spec b
    IsDiscreteValuationRing ((Spec (.of B)).presheaf.stalk b) :=
  let := isDomain_stalk_spec b
  let : b.asIdeal.IsPrime := b.isPrime
  have : IsDiscreteValuationRing (Localization.AtPrime b.asIdeal) :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain
      (A := CommRingCat.of B) hb _
  IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing
    (Spec.stalkIso (.of B) b).commRingCatIsoToRingEquiv.symm

omit [Module.Finite R ↥(integralClosure R K₁)] in
/-- **Smoothness of the normalized base change at a point over a solved bad point.**  Let `R` be
a Nagata Dedekind domain with fraction field `K`, let `g : Y ⟶ Spec R` be flat, quasi-compact
and locally of finite type with `Y` normal, and let `K₁ / K` be finite with
`B = integralClosure R K₁`.  Let `y` be a point of the normalization `Y₁` of `Y ×_{Spec R} Spec B`
which is a generic point of an irreducible component of its own fibre over `Spec B`, that fibre
not the generic one, and suppose `K₁` is a solution for the extension of discrete valuation rings
at the point `x` of `Y` below `y`.  Then `Y₁ ⟶ Spec B` is smooth at `y`. -/
theorem smoothAt_normalization_pullback_of_isSolutionForStalk (hR : IsNagataRing R)
    [QuasiCompact g]
    (hW : ∀ U : (pullback g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u}).Opens,
      IsCompact (U : Set (pullback g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u})) →
      (irreducibleComponents U).Finite)
    (y : (pullback g (Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(integralClosure R K₁)))) : Scheme.{u}).normalizationScheme hW)
    (hyne : ((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).base y).asIdeal ≠ ⊥)
    (hygen : (Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).asFiber y ∈
      genericPoints ↥((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).fiber
          ((Scheme.normalization _ hW ≫ pullback.snd g (Spec.map (CommRingCat.ofHom
            (algebraMap R ↥(integralClosure R K₁))))).base y)))
    (hs : (g.base ((pullback.fst g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).base
      ((Scheme.normalization _ hW).base y))).asIdeal ≠ ⊥)
    (hg : g.asFiber ((pullback.fst g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).base
      ((Scheme.normalization _ hW).base y)) ∈
      genericPoints ↥(g.fiber (g.base ((pullback.fst g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).base
          ((Scheme.normalization _ hW).base y)))))
    (hsol : IsSolutionForStalk K g ((pullback.fst g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).base
      ((Scheme.normalization _ hW).base y)) hs hg K₁) :
    InfinitesimalLifting.SmoothAt (Scheme.normalization _ hW ≫ pullback.snd g
      (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))) y := by
  have : Module.Finite R ↥(integralClosure R K₁) :=
    module_finite_integralClosure_of_isNagataRing K K₁ hR
  have : IsDedekindDomain ↥(integralClosure R K₁) :=
    isDedekindDomain_integralClosure_of_isNagataRing K K₁ hR
  have : IsFractionRing ↥(integralClosure R K₁) K₁ :=
    integralClosure.isFractionRing_of_finite_extension K K₁
  have : Module.Flat R ↥(integralClosure R K₁) := integralClosure.flat R K K₁
  have : IsLocalization (Algebra.algebraMapSubmonoid ↥(integralClosure R K₁)
      (nonZeroDivisors R)) K₁ :=
    IsIntegralClosure.isLocalization R K K₁ ↥(integralClosure R K₁)
  obtain ⟨hnorm, hflat, hlft, hqc⟩ :=
    flat_locallyOfFiniteType_quasiCompact_normalization_pullback K K₁ hR g
  have := hnorm
  have := hflat
  have := hlft
  have := hqc
  have := isDomain_stalk_spec ((Scheme.normalization _ hW ≫ pullback.snd g
    (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))).base y)
  have := isDiscreteValuationRing_stalk_spec ((Scheme.normalization _ hW ≫ pullback.snd g
    (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))).base y) hyne
  have := isDiscreteValuationRing_stalk_of_mem_genericPoints (Scheme.normalization _ hW ≫
    pullback.snd g (Spec.map (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))) y
    hyne hygen
  let : (g.base ((pullback.fst g (Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(integralClosure R K₁))))).base
    ((Scheme.normalization _ hW).base y))).asIdeal.IsPrime := PrimeSpectrum.isPrime _
  let := algebraStalkOfBase g ((pullback.fst g (Spec.map (CommRingCat.ofHom
    (algebraMap R ↥(integralClosure R K₁))))).base ((Scheme.normalization _ hW).base y))
  let := algebraStalkFractionRing K g ((pullback.fst g (Spec.map (CommRingCat.ofHom
    (algebraMap R ↥(integralClosure R K₁))))).base ((Scheme.normalization _ hW).base y))
  have := isScalarTower_algebraStalkFractionRing K g ((pullback.fst g (Spec.map
    (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))).base
      ((Scheme.normalization _ hW).base y))
  have := isDiscreteValuationRing_stalk_of_mem_genericPoints g ((pullback.fst g (Spec.map
    (CommRingCat.ofHom (algebraMap R ↥(integralClosure R K₁))))).base
      ((Scheme.normalization _ hW).base y)) hs hg
  let := algebraIntegralClosureCompositumOfBase R (Y.presheaf.stalk
    ((pullback.fst g (Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(integralClosure R K₁))))).base ((Scheme.normalization _ hW).base y))) K
    (FractionRing (Y.presheaf.stalk ((pullback.fst g (Spec.map (CommRingCat.ofHom
      (algebraMap R ↥(integralClosure R K₁))))).base ((Scheme.normalization _ hW).base y)))) K₁
  obtain ⟨p, hpmax, φ, hφ⟩ :=
    Scheme.exists_isMaximal_ringEquiv_stalk_normalizationScheme_pullback_localizationAtPrime_germ
      R (Y.presheaf.stalk ((pullback.fst g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).base ((Scheme.normalization _ hW).base y))) K
      (FractionRing (Y.presheaf.stalk ((pullback.fst g (Spec.map (CommRingCat.ofHom
        (algebraMap R ↥(integralClosure R K₁))))).base ((Scheme.normalization _ hW).base y))))
      ↥(integralClosure R K₁) K₁ g hW ((Scheme.normalization _ hW).base y)
      (RingEquiv.refl _) (fun _ ↦ rfl) y rfl
  exact smoothAt_of_formallySmoothNAdic_localizationAtPrime_germ _ y φ hφ
    (formallySmoothNAdic_localRingHom_of_isSolutionForStalk K g _ K₁ hs hg hsol p.asIdeal hpmax)

end Plumbing

end AlgebraicGeometry

end
