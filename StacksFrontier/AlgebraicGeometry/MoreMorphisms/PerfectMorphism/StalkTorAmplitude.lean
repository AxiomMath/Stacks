module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.LocalProperties.ProjectiveDimension
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Perfect.Morphism
public import StacksFrontier.Algebra.Homology.ProjectiveDimension
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.Module
public import StacksFrontier.Homology.PseudoCoherent.Coherent
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.FlatResolution
public import StacksFrontier.Homology.TorAmplitude.Local
public import StacksFrontier.Homology.TorAmplitude.ProjectiveResolutionModel
public import StacksFrontier.Homology.TorAmplitude.SingleOfCanonical
import StacksFrontier.Algebra.Homology.Resolution.ProjectiveDimensionTruncation
import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation

/-!
# Perfectness passes to the local rings

Let `f : X ⟶ S` be a perfect morphism of schemes.  Perfectness is defined, following condition
(2) of Stacks 0686, by a condition on the map of sections `Γ(S, V) ⟶ Γ(X, U)` over every
compatible pair of affine opens, of which the second half is that `Γ(X, U)` have finite Tor
dimension as a `Γ(S, V)`-module.  This file carries that second half down to the local rings:
for every point `x` of an affine open `U ⊆ f ⁻¹ᵁ V`, the localisation of `Γ(X, U)` at the prime
of `x` has finite Tor amplitude over the localisation of `Γ(S, V)` at the prime of `f x`, and
the bound is the one that already worked on the charts.

The statement is the local-ring half of the characterisation of perfectness in Stacks 069C.  It
is what a consumer that works at a stalk needs, since the stalk of a scheme at a point of an
affine open is exactly such a localisation, by
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`.

For a perfect *immersion* the bound can be improved: the stalk map is then surjective, so the
local ring upstairs is a cyclic module over the local ring downstairs, and over a Noetherian
local ring a finite module of finite flat dimension has finite projective dimension.  That is
the form Stacks 09PW consumes, and it is the last result below.

## Main results

* `AlgebraicGeometry.Perfect.hasTorAmplitudeAt_of_perfect`: the sections of the source over an
  affine chart, localised at a prime, have finite Tor amplitude over the sections of the target
  localised at the contracted prime.
* `AlgebraicGeometry.Perfect.under_primeIdealOf_eq`: the prime of a point in the source chart
  contracts to the prime of its image in the target chart, so the base ring in the previous
  result is the local ring of the target at the image point.
* `AlgebraicGeometry.Perfect.hasProjectiveDimensionLE_restrictScalars_ringEquiv`: projective
  dimension is carried along restriction of scalars by a ring isomorphism.
* `AlgebraicGeometry.Perfect.exists_hasProjectiveDimensionLE_stalk_of_perfect`: for a perfect
  immersion with locally Noetherian target, the local ring of the source has finite projective
  dimension over the local ring of the target.

## Implementation notes

Tor amplitude appears here in two renderings and both are needed.  Perfectness of a ring map
gives it against any certified derived tensor product
(`Algebra.Perfect.moduleHasFiniteTorDimension`), whereas the localisation theorem Stacks
0B67 is stated for the projective-resolution rendering
`StacksDraft.TorAmplitude.FaithfullyFlat.HasTorAmplitude`.  The two are compared by
`StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasTorAmplitude0DJF`, which needs a K-flat,
bounded-above, termwise flat model of the object; `hasTorAmplitude0DJF_single_of_canonical`
below supplies that model for a module placed in degree zero, by taking its projective
resolution.  Finite Tor dimension is read at `StacksDraft.TorAmplitude.canonicalTensorComparison`
and `StacksDraft.TorAmplitude.canonicalTensorIsLeftDerived` directly, rather than through
`StacksDraft.TorAmplitude.canonicalCertifiedDerivedTensoring`, because the latter is not exposed
and its field projections therefore do not reduce against the shape the comparison lemmas are
stated in.

**The two local rings are not the canonical localisations.** Stacks 0B67 is stated at
`Localization.AtPrime`, whereas the stalk of a scheme is only *a* localisation, so the passage
from the chart to the stalk is a comparison of two models.  Both models are identified with the
canonical ones by `IsLocalization.algEquiv`, and the square relating the two identifications to
the two structure maps is forced by the universal property of the localisation of the target's
ring of sections;  what feeds that universal property is the commuting square of germ maps,
stalk map and `Scheme.Hom.appLE`, which is `Scheme.Hom.germ_stalkMap` after unfolding
`Scheme.Hom.appLE`.  Projective dimension is then moved across the resulting ring isomorphism,
which is what `hasProjectiveDimensionLE_restrictScalars_ringEquiv` is for.

**The surjectivity hypothesis is where the immersion enters, and it is not decoration.** Finite
flat dimension does not imply finite projective dimension in general;  what makes the upgrade
work is that the module is *finite* over a Noetherian ring, so that it is pseudo-coherent and
Stacks 0657 applies.  Finiteness comes from surjectivity of the stalk map of an immersion, which
makes the local ring upstairs cyclic.

What is proved here is the implication from perfectness to finite Tor dimension of the local
rings, read on a chart. Stacks 069C itself is `AlgebraicGeometry.perfect_tfae` of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.RelativeTorDimensionClause`; its
implication (1) ⟹ (3) is `AlgebraicGeometry.Perfect.hasFiniteTorDimensionCanonical_stalk` of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.PerfectIffStalkTorDimension`,
which is
`AlgebraicGeometry.Perfect.hasTorAmplitudeAt_of_perfect` below transported from the chart to the
stalk.

## References

* [The Stacks Project, Lemma 37.61.11 (069C)](https://stacks.math.columbia.edu/tag/069C)
* [The Stacks Project, Lemma 37.61.1 (0686)](https://stacks.math.columbia.edu/tag/0686)
* [The Stacks Project, Definition 36.61.2 (0687)](https://stacks.math.columbia.edu/tag/0687)
* [The Stacks Project, Lemma 15.68.18 (0DJF)](https://stacks.math.columbia.edu/tag/0DJF)
* [The Stacks Project, Lemma 15.68.19 (0B67)](https://stacks.math.columbia.edu/tag/0B67)
* [The Stacks Project, Lemma 15.74.2 (0657)](https://stacks.math.columbia.edu/tag/0657)
* [The Stacks Project, Lemma 23.9.5 (09PW)](https://stacks.math.columbia.edu/tag/09PW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open StacksDraft.TorAmplitude

attribute [local instance] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Perfect

/-- **The prime of a point in a source chart contracts to the prime of its image.** For affine
opens `U ⊆ f ⁻¹ᵁ V` and `x ∈ U`, the prime of `Γ(X, U)` cut out by `x` lies over the prime of
`Γ(S, V)` cut out by `f x`.

This identifies the base ring of `AlgebraicGeometry.Perfect.hasTorAmplitudeAt_of_perfect`: the
localisation of `Γ(S, V)` at the contracted prime is the local ring of `S` at `f x`. -/
theorem under_primeIdealOf_eq {X S : Scheme.{u}} (f : X ⟶ S) {x : X}
    (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) (hxU : x ∈ U) :
    let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    Ideal.under Γ(S, V) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal =
      (hV.primeIdealOf ⟨f.base x, hUV hxU⟩).asIdeal := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  change Ideal.comap (algebraMap Γ(S, V) Γ(X, U)) _ = _
  rw [RingHom.algebraMap_toAlgebra]
  exact congrArg PrimeSpectrum.asIdeal
    (IsAffineOpen.comap_primeIdealOf_appLE V hV U hU hUV hxU)

/-- **Perfectness passes to the local rings.** Let `f : X ⟶ S` be perfect and let `U ⊆ f ⁻¹ᵁ V`
be a compatible pair of affine opens. Then there is an interval `[a, b]` such that for every
prime `q` of `Γ(X, U)` the localisation of `Γ(X, U)` at `q` has Tor amplitude in `[a, b]` over
the localisation of `Γ(S, V)` at the contraction of `q`.

This is the local-ring content of perfectness. The defining condition of
`AlgebraicGeometry.Perfect` gives finite Tor dimension of `Γ(X, U)` over `Γ(S, V)` on the charts
themselves; Stacks 0B67 is exactly the statement that such a bound may be read at every prime of
the source, with the *same* interval, over the localisation of the base at the contracted
prime. -/
theorem hasTorAmplitudeAt_of_perfect {X S : Scheme.{u}} (f : X ⟶ S) [Perfect f]
    (U : X.Opens) (hU : IsAffineOpen U) (V : S.Opens) (hV : IsAffineOpen V)
    (hUV : U ≤ f ⁻¹ᵁ V) :
    let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
    ∃ a b : ℤ, ∀ (q : Ideal Γ(X, U)) (_ : q.IsPrime),
      HasTorAmplitudeAt Γ(S, V)
        ((CochainComplex.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
          (ModuleCat.of Γ(X, U) Γ(X, U))) q a b := by
  let _ : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Perfect Γ(S, V) Γ(X, U) :=
    RingHom.perfect_algebraMap.mp (HasRingHomProperty.appLE @Perfect f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV)
  obtain ⟨a, b, hamp⟩ := Algebra.Perfect.moduleHasFiniteTorDimension (B := Γ(X, U))
    (canonicalTensorComparison Γ(S, V)) (canonicalTensorIsLeftDerived Γ(S, V))
  have hQ : HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct Γ(S, V)).tensor
      (canonicalTensorComparison Γ(S, V)) (canonicalTensorIsLeftDerived Γ(S, V))
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} Γ(S, V)) 0).obj
        (ModuleCat.of Γ(S, V) Γ(X, U)))) a b :=
    (hasTorAmplitude_of_iso (comparison := canonicalTensorComparison Γ(S, V))
      (isLeftDerived := canonicalTensorIsLeftDerived Γ(S, V))
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} Γ(S, V)) 0).app
        (ModuleCat.of Γ(S, V) Γ(X, U))).symm a b).mp hamp
  have hglobal : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).obj
        ((CochainComplex.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
          (ModuleCat.of Γ(X, U) Γ(X, U)))) a b := by
    have he :
        ((CochainComplex.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).obj
          ((CochainComplex.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
            (ModuleCat.of Γ(X, U) Γ(X, U)))) ≅
        (CochainComplex.singleFunctor (ModuleCat.{u} Γ(S, V)) 0).obj
          (ModuleCat.of Γ(S, V) Γ(X, U)) :=
      ((ModuleCat.restrictScalars.{u} (algebraMap Γ(S, V) Γ(X, U))).mapCochainComplexSingleFunctor
        0).app (ModuleCat.of Γ(X, U) Γ(X, U))
    exact hasTorAmplitude0DJF_of_isoComplex he.symm
      (hasTorAmplitude0DJF_single_of_canonical Γ(S, V) (ModuleCat.of Γ(S, V) Γ(X, U)) a b hQ)
  refine ⟨a, b, fun q _ => ?_⟩
  exact (hasTorAmplitude_iff_localized_at_primes_iff_maximals Γ(S, V) Γ(X, U)
    ((CochainComplex.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
      (ModuleCat.of Γ(X, U) Γ(X, U))) a b).1.mp hglobal q


/-- **Restriction of scalars along a ring isomorphism preserves projective dimension.**  The
functor is one half of `ModuleCat.restrictScalarsEquivalenceOfRingEquiv`, hence exact and
projective-preserving, so a bounded projective resolution is carried to one of the same length;
the induction is on the bound, through the syzygy short exact sequence. -/
theorem hasProjectiveDimensionLE_restrictScalars_ringEquiv {R S : Type u} [CommRing R]
    [CommRing S] (e : R ≃+* S) (n : ℕ) (M : ModuleCat.{u} S)
    [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE ((ModuleCat.restrictScalars.{u} (e : R →+* S)).obj M) n := by
  have hproj : (ModuleCat.restrictScalars.{u} (e : R →+* S)).PreservesProjectiveObjects :=
    Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv.{u} e).toAdjunction
  induction n generalizing M with
  | zero =>
      have hle : HasProjectiveDimensionLE M 0 := ‹_›
      simp only [HasProjectiveDimensionLE, zero_add] at hle ⊢
      rw [← projective_iff_hasProjectiveDimensionLT_one] at hle ⊢
      exact (ModuleCat.restrictScalars.{u} (e : R →+* S)).projective_obj_of_projective hle
  | succ n ih =>
      rcases ModuleCat.enoughProjectives.1 M with ⟨⟨P, f⟩⟩
      let T := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
      have T_exact : T.ShortExact := { exact := ShortComplex.exact_kernel f }
      let TS := T.map (ModuleCat.restrictScalars.{u} (e : R →+* S))
      have TS_exact : TS.ShortExact :=
        T_exact.map_of_exact (ModuleCat.restrictScalars.{u} (e : R →+* S))
      have hP2 : Projective T.X₂ := inferInstance
      have hTS2 : Projective TS.X₂ :=
        (ModuleCat.restrictScalars.{u} (e : R →+* S)).projective_obj_of_projective hP2
      have := (T_exact.hasProjectiveDimensionLT_X₃_iff n hP2).mp ‹_›
      exact (TS_exact.hasProjectiveDimensionLT_X₃_iff n hTS2).mpr (ih (kernel f))

/-- The converse of `hasTorAmplitude0DJF_single_of_canonical`: for a module in degree zero the
projective-resolution Tor amplitude of Stacks 0DJF gives Tor amplitude at the canonical derived
tensor product. -/
private theorem hasTorAmplitudeCanonical_single_of_0DJF
    (R : Type u) [CommRing R] (M : ModuleCat.{u} R) (a b : ℤ)
    (h : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) a b) :
    HasTorAmplitude
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
      (canonicalTensorComparison R) (canonicalTensorIsLeftDerived R)
      (DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M)) a b := by
  let P := FaithfullyFlat.projResComplex M
  have hPle : P.IsStrictlyLE 0 := by
    change CochainComplex.IsStrictlyLE
      ((CategoryTheory.ProjectiveResolution.of M).complex.extend
        ComplexShape.embeddingDownNat) 0
    infer_instance
  obtain ⟨hPKF, hPflat⟩ := projResComplex_kFlat R M
  have hPbound : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨0, fun i hi => by rw [CochainComplex.isStrictlyLE_iff] at hPle; exact hPle i hi⟩
  let q : P ⟶ (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M :=
    (CategoryTheory.ProjectiveResolution.of M).π'
  have hq : QuasiIso q := by
    dsimp [q]
    change QuasiIso
      (HomologicalComplex.extendMap (CategoryTheory.ProjectiveResolution.of M).π
        ComplexShape.embeddingDownNat ≫ _)
    have hπ' : QuasiIso (HomologicalComplex.extendMap
        (CategoryTheory.ProjectiveResolution.of M).π ComplexShape.embeddingDownNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff _ _).2
        (CategoryTheory.ProjectiveResolution.quasiIso _)
    infer_instance
  have hPtor : FaithfullyFlat.HasTorAmplitude P a b := by
    intro N i hi
    have := quasiIso_tensorRight_map (projResComplex_kFlat R N).1 q
    exact (homologyIsoOfQuasiIso
      ((tensorRight (FaithfullyFlat.projResComplex N)).map q) i).isZero_iff.mpr (h N i hi)
  exact (hasTorAmplitude_of_iso (comparison := canonicalTensorComparison R)
      (isLeftDerived := canonicalTensorIsLeftDerived R) (asIso (DerivedCategory.Q.map q)) a b).mp
    ((hasTorAmplitude_iff_hasTorAmplitude0DJF (canonicalTensorComparison R)
      (canonicalTensorIsLeftDerived R) P hPKF hPbound hPflat a b).mpr hPtor)


/-- The single complex of `B` with Tor amplitude in `[a, b]` at a prime `q` gives the single
complex of `B_q`, read over `A_p`, Tor amplitude in `[a, b]`. -/
private theorem hasTorAmplitude0DJF_single_localization_of_hasTorAmplitudeAt
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (q : Ideal B) [q.IsPrime] (a b : ℤ)
    (hamp : HasTorAmplitudeAt A
      ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) q a b) :
    let _ := Localization.AtPrime.algebraOfLiesOver (Ideal.under A q) q
    FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} (Localization.AtPrime (Ideal.under A q))) 0).obj
        (ModuleCat.of (Localization.AtPrime (Ideal.under A q)) (Localization.AtPrime q))) a b := by
  let p := Ideal.under A q
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  -- the localised single complex is the single complex of `B_q` read over `A_p`
  let ext := ModuleCat.extendScalars (algebraMap B (Localization.AtPrime q))
  let restr := ModuleCat.restrictScalars
    (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))
  have _ : ext.Additive :=
    (ModuleCat.extendRestrictScalarsAdj
      (algebraMap B (Localization.AtPrime q))).left_adjoint_additive
  let comp := CategoryTheory.Functor.comp ext restr
  let K := (CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)
  let K' : HomologicalComplex (ModuleCat.{u} B) (ComplexShape.up ℤ) := K
  let eComp := (CategoryTheory.Functor.mapHomologicalComplexCompIso
    (CategoryTheory.Iso.refl comp) (ComplexShape.up ℤ)).app K'
  let eSingleC := (HomologicalComplex.singleMapHomologicalComplex
    comp (ComplexShape.up ℤ) 0).app (ModuleCat.of B B)
  have hamp1 : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} (Localization.AtPrime p)) 0).obj
        (comp.obj (ModuleCat.of B B))) a b := by
    change FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.restrictScalars
        (algebraMap (Localization.AtPrime p) (Localization.AtPrime q))).obj
        ((CochainComplex.extendScalars (algebraMap B (Localization.AtPrime q))).obj K)) a b
      at hamp
    exact hasTorAmplitude0DJF_of_isoComplex (eComp ≪≫ eSingleC) hamp
  let eModule : (comp.obj (ModuleCat.of B B)) ≅
      ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q) := by
    let eExt : (ext.obj (ModuleCat.of B B)) ≅
        ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q) :=
      (LinearEquiv.trans
        (FaithfullyFlat.extendScalarsCarrierEquiv B (Localization.AtPrime q)
          (ModuleCat.of B B))
        (TensorProduct.AlgebraTensorModule.rid B (Localization.AtPrime q)
          (Localization.AtPrime q))).toModuleIso
    change restr.obj (ext.obj (ModuleCat.of B B)) ≅
      restr.obj (ModuleCat.of (Localization.AtPrime q) (Localization.AtPrime q))
    exact restr.mapIso eExt
  exact hasTorAmplitude0DJF_of_isoComplex
    ((CochainComplex.singleFunctor (ModuleCat.{u} (Localization.AtPrime p)) 0).mapIso eModule)
    hamp1

/-- **A perfect module has finite projective dimension.** If a module placed in degree zero is a
perfect object of the derived category, then it has finite projective dimension. -/
private theorem exists_hasProjectiveDimensionLE_of_isPerfect_single (R : Type u) [CommRing R]
    (M : Type u) [AddCommGroup M] [Module R M]
    (h : StacksDraft.Perfect.IsPerfect
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R M))) :
    ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  obtain ⟨d, F, hF, hzeroF⟩ :=
    (StacksDraft.Perfect.isPerfectModule_iff_exists_finite_projective_resolution (R := R) M).mp h
  exact ⟨d, F.hasProjectiveDimensionLE (fun i => (hF i).2) hzeroF⟩

/-- **From a Tor-amplitude bound at a prime to finite projective dimension of the local rings.**
If the structure of `B` as an `A`-module has Tor amplitude in `[a, b]` after localising at a
prime `q` of `B`, `A` is Noetherian, and the induced map of local rings is surjective, then
`B_q` has finite projective dimension over `A_p`, where `p` is the contraction of `q`.

Surjectivity is what makes `B_q` a finite — indeed cyclic — `A_p`-module, hence pseudo-coherent
over the Noetherian ring `A_p`; a pseudo-coherent object of finite Tor amplitude is perfect
(Stacks 0657) and so admits a finite resolution by finite projective modules. -/
private theorem exists_hasProjectiveDimensionLE_of_hasTorAmplitudeAt
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [IsNoetherianRing A]
    (q : Ideal B) [q.IsPrime] (a b : ℤ)
    (hamp : HasTorAmplitudeAt A
      ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) q a b)
    (hsurj : Function.Surjective (Localization.localRingHom (Ideal.under A q) q
      (algebraMap A B) Ideal.LiesOver.over)) :
    let _ := Localization.AtPrime.algebraOfLiesOver (Ideal.under A q) q
    ∃ n : ℕ, HasProjectiveDimensionLE
      (ModuleCat.of (Localization.AtPrime (Ideal.under A q)) (Localization.AtPrime q)) n := by
  let p := Ideal.under A q
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  have _ : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl _ ‹_›
  have hamp2 : FaithfullyFlat.HasTorAmplitude
      ((CochainComplex.singleFunctor (ModuleCat.{u} (Localization.AtPrime p)) 0).obj
        (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q))) a b :=
    hasTorAmplitude0DJF_single_localization_of_hasTorAmplitudeAt q a b hamp
  -- from Tor amplitude to a flat representative of the single object in the derived category
  have hrep := (hasTorAmplitude_iff_hasFlatRepresentative
    (canonicalTensorComparison (Localization.AtPrime p))
    (canonicalTensorIsLeftDerived (Localization.AtPrime p)) _ a b).mp
    (hasTorAmplitudeCanonical_single_of_0DJF (Localization.AtPrime p)
      (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q)) a b hamp2)
  have hrep' := hasFlatRepresentative_of_iso
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} (Localization.AtPrime p)) 0).app
      (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q))) hrep
  -- `B_q` is a cyclic, hence finite, `A_p`-module
  have hBfinite : Module.Finite (Localization.AtPrime p) (Localization.AtPrime q) :=
    Module.Finite.of_surjective
      (Algebra.linearMap (Localization.AtPrime p) (Localization.AtPrime q)) hsurj
  -- pseudo-coherence of the single object, and perfectness
  have hpc := (StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    ((DerivedCategory.singleFunctor (ModuleCat.{u} (Localization.AtPrime p)) 0).obj
      (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q)))
    0 (Localization.AtPrime q)).2.2.mpr hBfinite
  exact exists_hasProjectiveDimensionLE_of_isPerfect_single (Localization.AtPrime p)
    (Localization.AtPrime q)
    ((StacksDraft.Perfect.isPerfect_iff_pseudoCoherent_and_finiteTorDimension _).1.mpr
      ⟨hpc, a, b, hrep'⟩)

/-- **Finite projective dimension transfers along a compatible pair of ring isomorphisms.** If
`eR : R ≃+* P` and `φ : N ≃+* M` intertwine the structure maps `P → N` and `R → M`, then a
bound on the projective dimension of `N` over `P` is one for `M` over `R`. -/
private theorem hasProjectiveDimensionLE_of_ringEquiv {R P M N : Type u} [CommRing R] [CommRing P]
    [CommRing M] [CommRing N] [Algebra R M] [Algebra P N] (eR : R ≃+* P) (φ : N ≃+* M)
    (hkey : ∀ r : R, φ (algebraMap P N (eR r)) = algebraMap R M r) (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of P N) n] :
    HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  have hres := hasProjectiveDimensionLE_restrictScalars_ringEquiv eR n (ModuleCat.of P N)
  let _ : Module R N :=
    ((ModuleCat.restrictScalars.{u} (eR : R →+* P)).obj (ModuleCat.of P N)).isModule
  have hres' : HasProjectiveDimensionLE (ModuleCat.of R N) n := hres
  have hsm : ∀ (r : R) (y : N), r • y = algebraMap P N (eR r) * y := fun r y =>
    Algebra.smul_def (eR r) y
  let lin : N ≃ₗ[R] M :=
    { toFun := φ
      map_add' := map_add φ
      map_smul' := fun r y => by
        rw [hsm r y, map_mul, hkey r, RingHom.id_apply, Algebra.smul_def]
      invFun := φ.symm
      left_inv := φ.symm_apply_apply
      right_inv := φ.apply_symm_apply }
  exact hasProjectiveDimensionLT_of_iso lin.toModuleIso (n + 1)


/-- **Finite projective dimension of a localisation, read on any models of the two local rings.**
The previous result is stated at `Localization.AtPrime`; this moves it to arbitrary models `R` of
`A_p` and `M` of `B_q`, given that the square of structure maps commutes.  That is the form the
stalks of a scheme are presented in, by
`AlgebraicGeometry.IsAffineOpen.isLocalization_stalk`.

Both models are compared with the canonical localisations by `IsLocalization.algEquiv`, and the
comparison squares with the two structure maps are forced by the universal property of the
localisation of `A` at the contracted prime, which is where `htower` is used.  Projective
dimension is then carried across the ring isomorphism by
`AlgebraicGeometry.Perfect.hasProjectiveDimensionLE_restrictScalars_ringEquiv` and across the
resulting isomorphism of `R`-modules. -/
private theorem exists_hasProjectiveDimensionLE_of_hasTorAmplitudeAt_models
    {A B R M : Type u} [CommRing A] [CommRing B] [CommRing R] [CommRing M]
    [Algebra A B] [IsNoetherianRing A] [Algebra A R] [Algebra B M] [Algebra R M]
    (q : Ideal B) [q.IsPrime] (p : Ideal A) [p.IsPrime] (hp : Ideal.under A q = p)
    [IsLocalization.AtPrime R p] [IsLocalization.AtPrime M q]
    (htower : (algebraMap R M).comp (algebraMap A R) = (algebraMap B M).comp (algebraMap A B))
    (hsurj : Function.Surjective (algebraMap R M)) (a b : ℤ)
    (hamp : HasTorAmplitudeAt A
      ((CochainComplex.singleFunctor (ModuleCat.{u} B) 0).obj (ModuleCat.of B B)) q a b) :
    ∃ n : ℕ, HasProjectiveDimensionLE (ModuleCat.of R M) n := by
  subst hp
  let p := Ideal.under A q
  let _ : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    Localization.AtPrime.algebraOfLiesOver p q
  let e : Localization.AtPrime p ≃ₐ[A] R := IsLocalization.algEquiv p.primeCompl _ _
  let φ : Localization.AtPrime q ≃ₐ[B] M := IsLocalization.algEquiv q.primeCompl _ _
  let lrh : Localization.AtPrime p →+* Localization.AtPrime q :=
    Localization.localRingHom p q (algebraMap A B) Ideal.LiesOver.over
  -- the comparison square, by the universal property of `A_p`
  have hsq : (φ : Localization.AtPrime q →+* M).comp lrh =
      (algebraMap R M).comp (e : Localization.AtPrime p →+* R) := by
    refine IsLocalization.ringHom_ext p.primeCompl ?_
    ext x
    have hl : lrh (algebraMap A (Localization.AtPrime p) x) =
        algebraMap B (Localization.AtPrime q) (algebraMap A B x) :=
      Localization.localRingHom_to_map p q (algebraMap A B) Ideal.LiesOver.over x
    have hr : (e : Localization.AtPrime p →+* R) (algebraMap A (Localization.AtPrime p) x) =
        algebraMap A R x := e.commutes x
    have h2 := RingHom.congr_fun htower x
    simp only [RingHom.coe_comp, Function.comp_apply] at h2 ⊢
    rw [hl, hr]
    exact (φ.commutes _).trans h2.symm
  have hlrh : Function.Surjective lrh := by
    have hcomp : Function.Surjective ((φ : Localization.AtPrime q →+* M).comp lrh) := by
      rw [hsq]
      exact hsurj.comp e.surjective
    intro y
    obtain ⟨x, hx⟩ := hcomp (φ y)
    exact ⟨x, φ.injective hx⟩
  obtain ⟨n, hn⟩ := exists_hasProjectiveDimensionLE_of_hasTorAmplitudeAt q a b hamp hlrh
  -- carry the bound across the ring isomorphism and then across the module isomorphism
  have _ : HasProjectiveDimensionLE
      (ModuleCat.of (Localization.AtPrime p) (Localization.AtPrime q)) n := hn
  let eR : R ≃+* Localization.AtPrime p := e.toRingEquiv.symm
  have hkey : ∀ r : R, φ (lrh (eR r)) = algebraMap R M r := fun r => by
    simpa [eR] using RingHom.congr_fun hsq (eR r)
  exact ⟨n, hasProjectiveDimensionLE_of_ringEquiv eR φ.toRingEquiv hkey n⟩


/-- **The local ring of the source of a perfect immersion has finite projective dimension over
the local ring of the target.** Let `i : Z ⟶ Y` be a perfect immersion of schemes with `Y`
locally Noetherian, and let `z : Z`. Then `O_{Z, z}`, as a module over `O_{Y, i z}` through the
stalk map, has finite projective dimension.

This is the input that Stacks 09PW consumes in the proof of Stacks 09RK, where the pair of
nested ideals is the kernel of the stalk map of `j` inside the kernel of the stalk map of
`i ≫ j`.

Both hypotheses on `i` are used, and for different things: perfectness supplies the Tor-amplitude
bound on an affine chart, which
`AlgebraicGeometry.Perfect.hasTorAmplitudeAt_of_perfect` carries to the local rings; and the
immersion hypothesis makes the stalk map surjective, so that `O_{Z, z}` is a cyclic — hence
finite — module over the Noetherian local ring `O_{Y, i z}`, which is what upgrades a bound on
the flat dimension to one on the projective dimension. -/
theorem exists_hasProjectiveDimensionLE_stalk_of_perfect {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsImmersion i] [Perfect i] [IsLocallyNoetherian Y] (z : Z) :
    let _ : Algebra (Y.presheaf.stalk (i.base z)) (Z.presheaf.stalk z) :=
      (i.stalkMap z).hom.toAlgebra
    ∃ n : ℕ, HasProjectiveDimensionLE
      (ModuleCat.of (Y.presheaf.stalk (i.base z)) (Z.presheaf.stalk z)) n := by
  let _ : Algebra (Y.presheaf.stalk (i.base z)) (Z.presheaf.stalk z) :=
    (i.stalkMap z).hom.toAlgebra
  obtain ⟨_, ⟨W, hW, rfl⟩, hzW, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (i.base z)) isOpen_univ
  obtain ⟨_, ⟨U, hU, rfl⟩, hzU, hUW⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open
    hzW (i ⁻¹ᵁ W).2
  let _ : Algebra Γ(Y, W) Γ(Z, U) := (i.appLE W U hUW).hom.toAlgebra
  let _ := Y.presheaf.algebra_section_stalk (⟨i.base z, hzW⟩ : W)
  let _ := Z.presheaf.algebra_section_stalk (⟨z, hzU⟩ : U)
  have _ : IsNoetherianRing Γ(Y, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have halgR : (algebraMap Γ(Y, W) (Y.presheaf.stalk (i.base z)))
      = (Y.presheaf.germ W (i.base z) hzW).hom := RingHom.algebraMap_toAlgebra _
  have halgM : (algebraMap Γ(Z, U) (Z.presheaf.stalk z))
      = (Z.presheaf.germ U z hzU).hom := RingHom.algebraMap_toAlgebra _
  have halgRM : (algebraMap (Y.presheaf.stalk (i.base z)) (Z.presheaf.stalk z))
      = (i.stalkMap z).hom := RingHom.algebraMap_toAlgebra _
  have halgAB : (algebraMap Γ(Y, W) Γ(Z, U)) = (i.appLE W U hUW).hom :=
    RingHom.algebraMap_toAlgebra _
  have hpq : Ideal.under Γ(Y, W) (hU.primeIdealOf ⟨z, hzU⟩).asIdeal
      = (hW.primeIdealOf ⟨i.base z, hzW⟩).asIdeal :=
    under_primeIdealOf_eq i U hU W hW hUW hzU
  have _ : IsLocalization.AtPrime (Y.presheaf.stalk (i.base z))
      (hW.primeIdealOf ⟨i.base z, hzW⟩).asIdeal := hW.isLocalization_stalk ⟨i.base z, hzW⟩
  have _ : IsLocalization.AtPrime (Z.presheaf.stalk z)
      (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := hU.isLocalization_stalk ⟨z, hzU⟩
  have htower : (algebraMap (Y.presheaf.stalk (i.base z)) (Z.presheaf.stalk z)).comp
        (algebraMap Γ(Y, W) (Y.presheaf.stalk (i.base z)))
      = (algebraMap Γ(Z, U) (Z.presheaf.stalk z)).comp (algebraMap Γ(Y, W) Γ(Z, U)) := by
    have hsq : i.appLE W U hUW ≫ Z.presheaf.germ U z hzU
        = Y.presheaf.germ W (i.base z) hzW ≫ i.stalkMap z := by
      simp only [Scheme.Hom.appLE, Category.assoc, Z.presheaf.germ_res,
        ← Scheme.Hom.germ_stalkMap i W z hzW]
    ext s
    simp only [RingHom.coe_comp, Function.comp_apply, halgR, halgM, halgRM, halgAB]
    exact (ConcreteCategory.congr_hom hsq s).symm
  have hsurj : Function.Surjective
      (algebraMap (Y.presheaf.stalk (i.base z)) (Z.presheaf.stalk z)) := by
    rw [halgRM]
    exact i.stalkMap_surjective z
  obtain ⟨a, b, hamp⟩ := hasTorAmplitudeAt_of_perfect i U hU W hW hUW
  exact exists_hasProjectiveDimensionLE_of_hasTorAmplitudeAt_models
    (hU.primeIdealOf ⟨z, hzU⟩).asIdeal (hW.primeIdealOf ⟨i.base z, hzW⟩).asIdeal hpq
    htower hsurj a b (hamp (hU.primeIdealOf ⟨z, hzU⟩).asIdeal inferInstance)

end AlgebraicGeometry.Perfect





end
