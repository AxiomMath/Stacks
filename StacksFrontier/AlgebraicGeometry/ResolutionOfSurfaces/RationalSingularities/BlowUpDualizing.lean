module

public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.BlowupTwist
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
import StacksCore.Tactic.StacksAttribute

/-!
# The dualizing module on the blowup of a surface singularity at its closed point

Let `(A, 𝔪)` be a Noetherian local ring, let `X` be the blowup of `Spec(A)` in `𝔪` with
exceptional divisor `i : E ⟶ X`, and let `𝒪_X(n)` be the `n`-th power of the twisting sheaf
`AlgebraicGeometry.blowUpTwist` of the blowup, `𝒪_E(n)` its restriction to `E`. For `ω_X` a
dualizing module on `X` and `ω_E` one on `E`, [Stacks, Tag 0B64] asserts, in Situation
[Stacks, Tag 0B4W] with `ω_A` a dualizing module for `A` and `A` not regular, that

1. `ω_E = ω_X|_E ⊗ 𝒪_E(-1)`, and
2. `H¹(X, ω_X(n)) = 0` for `n ≥ 0`.

This file proves the steps of both from the inputs listed below; the clauses themselves are
registered, for the normalized dualizing module, at
`AlgebraicGeometry.BlowUpDualizing.nonempty_dualizingSheafOverField_iso_curveTwist` and
`AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_schemeTwist_of_dualizingNormalization`.
Twists are
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.twistModule` at `𝒪_X(-1)`, and cohomology is
the `δ`-functor `Stacks.AlgebraicGeometry.HyperplaneTwistSequence.cohomologyDeltaFunctor`, the
right derived global sections of [Stacks, Tag 089W].

## Main definitions

* `AlgebraicGeometry.BlowUpDualizing.twistSheaf` and `.curveTwistSheaf`: `𝒪_X(n)` and `𝒪_E(n)`.
* `AlgebraicGeometry.BlowUpDualizing.schemeTwist` and `.curveTwist`: `ℱ(n)` on `X` and on `E`.
* `AlgebraicGeometry.BlowUpDualizing.conormalSheaf`: the conormal sheaf `ℐ_E|_E`.
* `AlgebraicGeometry.BlowUpDualizing.ExceptionalAdjunction`: the adjunction formula for the
  effective Cartier divisor `E ⊂ X`, carried.

## Main results

* `AlgebraicGeometry.BlowUpDualizing.nonempty_pullback_dualizing_iso_curveTwist` and
  `.nonempty_pullback_curveTwist_iso`: `ω_X|_E ≅ ω_E(1)` and `ω_X|_E(n) ≅ ω_E(n+1)`, derived
  from the isomorphism of clause (1).
* `AlgebraicGeometry.BlowUpDualizing.isZero_firstCohomology_dualizingTwist`: the conclusion of
  **clause (2)**, with the curve vanishing stated for the restricted module `ω_X|_E(n)`.
* `AlgebraicGeometry.BlowUpDualizing.twistSheafOneIso` and `.twistSheafNatIso`: `𝒪_X(1)` is
  `AlgebraicGeometry.blowUpTwist` of the blowup and `𝒪_X(n)` is its `n`-th tensor power for
  `n ≥ 0`; `.pullbackTwistSheafIso`: `𝒪_E(n)` is the restriction of `𝒪_X(n)`.
* `AlgebraicGeometry.BlowUpDualizing.conormalSheafIso`,
  `.conormalTensorTwistNegOneIso` and `.isInvertibleModule_conormalSheaf`: the conormal sheaf is
  `𝒪_E(1)`, `𝒪_E(-1)` is a tensor inverse of it, and it is invertible.

## Implementation notes

**`ω_X` and `ω_E` are parameters with a predicate hypothesis, not constructions.** The existence
of the dualizing module is gated in this development on the twisted inverse image `f^!`: Tag 0A9E
is absent and Tag 0B6S is nowhere tagged. So, following
`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingComplex.lean` and
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/RationalSingularities/DualizingTrace.lean`,
the dualizing modules enter as parameters carrying `Stacks.Duality.IsDualizingModule`
([Stacks, Tag 0B4R]) — the hypotheses `_hωX` and `_hωE`, which pin down what the parameters are
without being used in the proofs — and the duality statements about them are hypotheses too.
Nothing below asserts anything about `ω_X` or `ω_E` beyond what those hypotheses give.

**The adjunction datum.** `ExceptionalAdjunction` is the adjunction formula for the effective
Cartier divisor `E ⊂ X`: a normal sheaf `𝒩`, inverse to the conormal sheaf `ℐ_E|_E`, with
`ω_E ≅ ω_X|_E ⊗ 𝒩`. That is [Stacks, Tag 0A9X] followed by [Stacks, Tag 0AA4] at `ω_X^• = ω_X[2]`
and `ω_E^• = ω_E[1]` ([Stacks, Remark 0B4R]). Both tags are formalized only as *maps*:
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierDerivedSheafHom.lean:304` states Tag 0AA4's
canonical map `Li^*K ⊗ 𝒩[-1] ⟶ R ℰom(𝒪_D, K)` and says in its attribute that it is not proved to
be an isomorphism, and
`StacksFrontier/AlgebraicGeometry/Duality/ClosedImmersionRightAdjointSheafHom.lean:198` carries part
(1) of Tag 0A6H as a hypothesis. The other input, taken by the conormal-sheaf results below, is
`hexc`, the identification `ℐ_E ≅ 𝒪_X(1)` of part (3) of [Stacks, Tag 02OS]; its absence is
recorded in the module documentation of
`StacksFrontier/AlgebraicGeometry/Blowup/ExceptionalTwist.lean:40` and
`StacksFrontier/AlgebraicGeometry/Spaces/BlowupIsomorphismOffCentre.lean:66`.

From these the normal sheaf is identified with `𝒪_E(-1)`:
`hexc` restricts to `ℐ_E|_E ≅ 𝒪_E(1)` because pullback commutes with the integer tensor powers of
an invertible module, `𝒪_E(1) ⊗ 𝒪_E(-1) ≅ 𝒪_E` by the addition law for the powers, and a tensor
inverse is unique up to isomorphism, so `𝒩 ≅ 𝒪_E(-1)`.

**The two gaps in the source's proof of clause (2).**

*The sequences are not left exact for free.* The source writes down
`0 ⟶ ω_X(n+1) ⟶ ω_X(n) ⟶ i_*ω_E(n+1) ⟶ 0` for every `n` without comment. Tensoring the
unconditional ideal sequence `0 ⟶ ℐ_E ⟶ 𝒪_X ⟶ i_*𝒪_E ⟶ 0`
(`Stacks.IdealSheafSequence.divisorIdeal_shortExact`, [Stacks, Tag 0C6K]) with `ω_X(n)` is only
right exact; exactness on the left is the statement that the local equation of `E` is a
nonzerodivisor on `ω_X`. Here *one* sequence is carried — the untwisted
`0 ⟶ ω_X(1) ⟶ ω_X ⟶ i_*(ω_X|_E) ⟶ 0`, as the data `f`, `g`, `w`, `hS`, exactly as
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/HyperplaneTwistSequence.lean` carries
[Stacks, Tag 08A0] — and the whole family is *derived* from it: tensoring by the invertible
`𝒪_X(n)` is an equivalence of categories, hence exact, and the projection formula at a closed
immersion identifies the third term. The irreducible content of the gap is therefore the
monomorphy in `hS`, which is the nonzerodivisor statement; its proof needs `ω_X` to be a maximal
Cohen--Macaulay module on the normal surface `X`, and this development has `IsDualizingModule` but
no theory relating it to depth, so that step is not formalized.

*`ω_X|_E = ω_E(1)` is not assumed.* It is derived from clause (1):
`nonempty_pullback_dualizing_iso_curveTwist` twists the clause-(1) isomorphism once, and
`nonempty_pullback_curveTwist_iso` gives `ω_X|_E(n) ≅ ω_E(n+1)`, which is what turns the third
term of the twisted sequence into the module [Stacks, Tag 0B62] speaks about.

**What clause (2) carries besides the sequence.** `hcurve` is `H¹(E, ω_X|_E(n)) = 0`; under
`nonempty_pullback_curveTwist_iso` this is `H¹(E, ω_E(n+1)) = 0`, the
conclusion of [Stacks, Tag 0B62] — proved at
`StacksFrontier/AlgebraicGeometry/Curves/VanishingResults/DualizingTwist.lean:195`, itself carrying
duality and a global-generation step, and needing for `E` both Situation [Stacks, Tag 0B5D] and
the global generation and nontriviality of `𝒪_E(n+1)`, which are clauses (2) and (3) of
[Stacks, Tag 0B63]; of that tag only clause (1) is proved, in `ExceptionalCurve.lean`.
`heventual` is the conclusion of [Stacks, Tag 02O1] — proved at
`StacksFrontier/AlgebraicGeometry/RelativeAmpleTwistVanishing/Basic.lean:227`, carrying its own
affine-base hypothesis — applied to the relatively ample `AlgebraicGeometry.blowUpTwist`, whose
powers are the twists used here by `twistSheafNatIso`; what is not assembled is the affine-base
comparison [Stacks, Tag 01XK]
(`Stacks.Cohomology.AffineBase.cohomologyIsoSectionsRightDerivedPushforward`) between the higher
direct images of that tag and the cohomology of this file. `hqc` is the quasi-coherence side
condition of [Stacks, Tag 089W].

Everything else in clause (2) is proved: the twisted sequences, the transport of the curve
vanishing to `X` along [Stacks, Tag 089W], the step from vanishing at `n + 1` to vanishing at `n`
through the long exact sequence of the cohomological `δ`-functor, and the downward induction.

**Clause (3) is not treated.** It is the surjectivity of `f^*ω_A ⟶ ω_X` of
[Stacks, Tag 0BBU], whose formalized form
(`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/RationalSingularities/DualizingTrace.lean:132`)
carries Grauert--Riemenschneider vanishing [Stacks, Tag 0AXD] as a hypothesis, and Tag 0AXD has no
attribute site in this development; the canonical map `f^*ω_A ⟶ ω_X` itself is recorded there as
not covered. The source's argument is also incomplete: it proves generation only along `E`, and
needs `f` to be an isomorphism over `Spec(A) ∖ {𝔪}` to conclude at the points off `E`.

**The nonregularity of `A` is not used**, in either clause. It enters [Stacks, Tag 0B63] only
through the strict inequality `deg 𝒪_E(1) ≥ 2`, which feeds the global generation of `𝒪_E(n+1)`
inside `hcurveE`; here that is part of the carried hypothesis, so `A` need only be local.

## References

* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0B63](https://stacks.math.columbia.edu/tag/0B63)
* [Stacks Project, Tag 0B62](https://stacks.math.columbia.edu/tag/0B62)
* [Stacks Project, Tag 0AA4](https://stacks.math.columbia.edu/tag/0AA4)
* [Stacks Project, Tag 0A9X](https://stacks.math.columbia.edu/tag/0A9X)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 02O1](https://stacks.math.columbia.edu/tag/02O1)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 0C6K](https://stacks.math.columbia.edu/tag/0C6K)
* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Ample Stacks.RelativeVeryAmple
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.Cohomology.FormalFunctions (cohomologyDeltaFunctor)

universe u

namespace AlgebraicGeometry.BlowUpDualizing

/-! ### The blowup, its exceptional curve, and the twists -/

variable (A : Type u) [CommRing A] [IsLocalRing A]

/-- The ideal sheaf of the closed point of `Spec(A)`, the centre of the blowup. -/
abbrev centre : (Spec (.of A)).IdealSheafData := (Stacks.Blowup.residuePoint A).ker

/-- `X`, the blowup of `Spec(A)` in the maximal ideal. -/
@[sga "6 X 7.17.4" "blow-up of Spec O_{S"]
abbrev blowUpScheme : Scheme.{u} := blowUp (centre A)

/-- `E`, the exceptional divisor of the blowup. -/
abbrev exceptionalCurve : Scheme.{u} := exceptionalDivisor (centre A)

/-- The closed immersion `i : E ⟶ X` of the exceptional divisor. -/
abbrev exceptionalImmersion : exceptionalCurve A ⟶ blowUpScheme A :=
  (exceptionalIdeal (centre A)).subschemeι

/-- `𝒪_X(-1)`, the inverse of the twisting sheaf of the blowup. -/
abbrev twistNegOne : (blowUpScheme A).Modules :=
  tensorPowModule (blowUpScheme A) (blowUpTwist (centre A) 1) (-1)

/-- `𝒪_E(-1)`, the restriction of `𝒪_X(-1)` to the exceptional curve. -/
abbrev curveTwistNegOne : (exceptionalCurve A).Modules :=
  (Scheme.Modules.pullback (exceptionalImmersion A)).obj (twistNegOne A)

/-- `ℱ(n) = ℱ ⊗ 𝒪_X(n)` for an `𝒪_X`-module `ℱ`. -/
abbrev schemeTwist (F : (blowUpScheme A).Modules) (n : ℤ) : (blowUpScheme A).Modules :=
  twistModule (blowUpScheme A) (twistNegOne A) F (-n)

/-- `𝒢(n) = 𝒢 ⊗ 𝒪_E(n)` for an `𝒪_E`-module `𝒢`. -/
abbrev curveTwist (G : (exceptionalCurve A).Modules) (n : ℤ) : (exceptionalCurve A).Modules :=
  twistModule (exceptionalCurve A) (curveTwistNegOne A) G (-n)

/-- `𝒪_X(n)`, the `n`-th power of the twisting sheaf of the blowup. -/
abbrev twistSheaf (n : ℤ) : (blowUpScheme A).Modules :=
  tensorPowModule (blowUpScheme A) (twistNegOne A) (-n)

/-- `𝒪_E(n)`, the restriction of `𝒪_X(n)` to the exceptional curve. -/
abbrev curveTwistSheaf (n : ℤ) : (exceptionalCurve A).Modules :=
  tensorPowModule (exceptionalCurve A) (curveTwistNegOne A) (-n)

/-- `𝒪_E(n)` is the restriction of `𝒪_X(n)`: pullback commutes with the tensor powers of an
invertible module. -/
def pullbackTwistSheafIso (n : ℤ) :
    (Scheme.Modules.pullback (exceptionalImmersion A)).obj (twistSheaf A n) ≅
      curveTwistSheaf A n :=
  pullbackTensorPowModuleIntIso (exceptionalImmersion A) (twistNegOne A) (-n)

/-- `𝒪_X(1)` is the twisting sheaf `AlgebraicGeometry.blowUpTwist` of the blowup: both are
tensor inverses of `𝒪_X(-1)`. -/
def twistSheafOneIso : twistSheaf A 1 ≅ blowUpTwist (centre A) 1 :=
  Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso (blowUpScheme A)
    (twistSheaf A 1) (blowUpTwist (centre A) 1) (twistNegOne A)
    (tensorModulesMapIso (blowUpScheme A) (Iso.refl _)
        (tensorPowModuleOneIso (blowUpScheme A) (twistNegOne A)).symm ≪≫
      tensorPowModuleAddIso (blowUpScheme A) (twistNegOne A) (-1) 1 ≪≫
      tensorPowModuleCongr (blowUpScheme A) (twistNegOne A) (show (-1 : ℤ) + 1 = 0 by ring) ≪≫
      tensorPowModuleZeroIso (blowUpScheme A) (twistNegOne A))
    (tensorModulesMapIso (blowUpScheme A)
        (tensorPowModuleOneIso (blowUpScheme A) (blowUpTwist (centre A) 1)).symm (Iso.refl _) ≪≫
      tensorPowModuleAddIso (blowUpScheme A) (blowUpTwist (centre A) 1) 1 (-1) ≪≫
      tensorPowModuleCongr (blowUpScheme A) (blowUpTwist (centre A) 1)
        (show (1 : ℤ) + -1 = 0 by ring) ≪≫
      tensorPowModuleZeroIso (blowUpScheme A) (blowUpTwist (centre A) 1))

/-- `𝒪_X(n)` is the `n`-th tensor power of the twisting sheaf of the blowup, for `n ≥ 0`: both
are tensor inverses of `𝒪_X(-1)^{⊗ n}`. -/
def twistSheafNatIso (n : ℕ) :
    twistSheaf A (n : ℤ) ≅ tensorPowModule (blowUpScheme A) (blowUpTwist (centre A) 1) (n : ℤ) :=
  Stacks.AlgebraicGeometry.ProjTwistTensorPow.isoOfTensorUnitIso (blowUpScheme A)
    (twistSheaf A (n : ℤ))
    (tensorPowModule (blowUpScheme A) (blowUpTwist (centre A) 1) (n : ℤ))
    (tensorPowModule (blowUpScheme A) (twistNegOne A) (n : ℤ))
    (tensorPowModuleAddIso (blowUpScheme A) (twistNegOne A) (-(n : ℤ)) (n : ℤ) ≪≫
      tensorPowModuleCongr (blowUpScheme A) (twistNegOne A)
        (show -(n : ℤ) + (n : ℤ) = 0 by ring) ≪≫
      tensorPowModuleZeroIso (blowUpScheme A) (twistNegOne A))
    (tensorModulesMapIso (blowUpScheme A) (Iso.refl _)
        (tensorPowModulePowIso (blowUpScheme A) (blowUpTwist (centre A) 1) (-1) n ≪≫
          tensorPowModuleCongr (blowUpScheme A) (blowUpTwist (centre A) 1)
            (show (-1 : ℤ) * (n : ℤ) = -(n : ℤ) by ring)) ≪≫
      tensorPowModuleAddIso (blowUpScheme A) (blowUpTwist (centre A) 1) (n : ℤ) (-(n : ℤ)) ≪≫
      tensorPowModuleCongr (blowUpScheme A) (blowUpTwist (centre A) 1)
        (show (n : ℤ) + -(n : ℤ) = 0 by ring) ≪≫
      tensorPowModuleZeroIso (blowUpScheme A) (blowUpTwist (centre A) 1))

/-- `𝒪_E(a) ⊗ 𝒪_E(b) ≅ 𝒪_E(a + b)`. -/
def curveTwistSheafAddIso (a b : ℤ) :
    tensorModules (exceptionalCurve A) (curveTwistSheaf A a) (curveTwistSheaf A b) ≅
      curveTwistSheaf A (a + b) :=
  tensorPowModuleAddIso (exceptionalCurve A) (curveTwistNegOne A) (-a) (-b) ≪≫
    tensorPowModuleCongr (exceptionalCurve A) (curveTwistNegOne A)
      (show -a + -b = -(a + b) by ring)

/-- Reindexing of `𝒪_E(n)` along an equality of degrees. -/
def curveTwistSheafCongr {a b : ℤ} (h : a = b) : curveTwistSheaf A a ≅ curveTwistSheaf A b :=
  tensorPowModuleCongr (exceptionalCurve A) (curveTwistNegOne A) (by rw [h])

/-- `𝒪_E(0) ≅ 𝒪_E`. -/
def curveTwistSheafZeroIso : curveTwistSheaf A 0 ≅ unitModule (exceptionalCurve A) :=
  tensorPowModuleCongr (exceptionalCurve A) (curveTwistNegOne A) (show -(0 : ℤ) = 0 by ring) ≪≫
    tensorPowModuleZeroIso (exceptionalCurve A) (curveTwistNegOne A)

/-- `𝒢(0) ≅ 𝒢`. -/
def curveTwistZeroIso (G : (exceptionalCurve A).Modules) : curveTwist A G 0 ≅ G :=
  tensorModulesMapIso (exceptionalCurve A) (Iso.refl G)
      (tensorPowModuleCongr (exceptionalCurve A) (curveTwistNegOne A)
        (show -(0 : ℤ) = 0 by ring) ≪≫
      tensorPowModuleZeroIso (exceptionalCurve A) (curveTwistNegOne A)) ≪≫
    Stacks.SheafOfModules.tensorLeftFunctorObjUnitIso (exceptionalCurve A).presheaf
      (Stacks.SheafInternalHom.isSheaf_structureRingPresheaf (exceptionalCurve A)) G

/-- `𝒢(a)(b) ≅ 𝒢(a + b)`. -/
def curveTwistAddIso (G : (exceptionalCurve A).Modules) (a b : ℤ) :
    curveTwist A (curveTwist A G a) b ≅ curveTwist A G (a + b) :=
  twistTwistIso (exceptionalCurve A) (curveTwistNegOne A) G (-a) (-b) ≪≫
    twistModuleCongr (exceptionalCurve A) (curveTwistNegOne A) G
      (show -a + -b = -(a + b) by ring)

/-! ### The conormal sheaf of the exceptional curve -/

/-- `ℐ_E`, the ideal sheaf of the exceptional divisor, as an `𝒪_X`-module. -/
abbrev exceptionalIdealModule : (blowUpScheme A).Modules :=
  Stacks.ClosedImmersion.idealSheaf (exceptionalImmersion A).toLRSHom.toShHom

/-- `ℐ_E|_E`, the conormal sheaf of the exceptional curve. -/
abbrev conormalSheaf : (exceptionalCurve A).Modules :=
  (Scheme.Modules.pullback (exceptionalImmersion A)).obj (exceptionalIdealModule A)

variable {A}

/-- The conormal sheaf of the exceptional curve is `𝒪_E(1)`, granted the identification
`ℐ_E ≅ 𝒪_X(1)` of the ideal sheaf of the exceptional divisor with the twisting sheaf. -/
def conormalSheafIso (hexc : exceptionalIdealModule A ≅ twistSheaf A 1) :
    conormalSheaf A ≅ curveTwistSheaf A 1 :=
  (Scheme.Modules.pullback (exceptionalImmersion A)).mapIso hexc ≪≫ pullbackTwistSheafIso A 1

/-- `𝒪_E(-1)` is a tensor inverse of the conormal sheaf of the exceptional curve. -/
def conormalTensorTwistNegOneIso (hexc : exceptionalIdealModule A ≅ twistSheaf A 1) :
    tensorModules (exceptionalCurve A) (curveTwistSheaf A (-1)) (conormalSheaf A) ≅
      unitModule (exceptionalCurve A) :=
  tensorModulesMapIso (exceptionalCurve A) (Iso.refl _) (conormalSheafIso hexc) ≪≫
    curveTwistSheafAddIso A (-1) 1 ≪≫
    curveTwistSheafCongr A (show (-1 : ℤ) + 1 = 0 by ring) ≪≫ curveTwistSheafZeroIso A

/-- The conormal sheaf of the exceptional curve is invertible, granted `ℐ_E ≅ 𝒪_X(1)`. -/
theorem isInvertibleModule_conormalSheaf (hexc : exceptionalIdealModule A ≅ twistSheaf A 1) :
    IsInvertibleModule (exceptionalCurve A) (conormalSheaf A) :=
  Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso (conormalSheafIso hexc).symm

/-! ### Clause (1): the dualizing sheaf of the exceptional curve -/

variable (A)

/-- The blowup of the spectrum of a Noetherian local ring is locally Noetherian: the blowup
morphism is proper, hence locally of finite type. -/
theorem isLocallyNoetherian_blowUpScheme [IsNoetherianRing A] :
    IsLocallyNoetherian (blowUpScheme A) :=
  let : IsProper (blowUpToBase (centre A)) := isProper_blowUpToBase (centre A)
  LocallyOfFiniteType.isLocallyNoetherian (blowUpToBase (centre A))

/-- The exceptional curve of the blowup of the spectrum of a Noetherian local ring is locally
Noetherian: it is a closed subscheme of the blowup. -/
theorem isLocallyNoetherian_exceptionalCurve [IsNoetherianRing A] :
    IsLocallyNoetherian (exceptionalCurve A) :=
  let : IsLocallyNoetherian (blowUpScheme A) := isLocallyNoetherian_blowUpScheme A
  LocallyOfFiniteType.isLocallyNoetherian (exceptionalIdeal (centre A)).subschemeι

/-- **The adjunction formula for the exceptional divisor**, as [Stacks, Tag 0A9X] and
[Stacks, Tag 0AA4] deliver it after the normalization of [Stacks, Remark 0B4R]: the dualizing
sheaf of `E` is the restriction of the dualizing module of `X` twisted by the normal sheaf. -/
structure ExceptionalAdjunction (ωX : (blowUpScheme A).Modules)
    (ωE : (exceptionalCurve A).Modules) where
  /-- The normal sheaf `𝒩_{E/X}` of the exceptional curve. -/
  normal : (exceptionalCurve A).Modules
  /-- The normal sheaf is invertible. -/
  isInvertible : IsInvertibleModule (exceptionalCurve A) normal
  /-- The normal sheaf is a tensor inverse of the conormal sheaf `ℐ_E|_E`. -/
  inverse : tensorModules (exceptionalCurve A) normal (conormalSheaf A) ≅
    unitModule (exceptionalCurve A)
  /-- `ω_E ≅ ω_X|_E ⊗ 𝒩_{E/X}`. -/
  formula : ωE ≅ tensorModules (exceptionalCurve A)
    ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) normal

variable {A}

/-- Reindexing of `𝒢(n)` along an equality of degrees. -/
def curveTwistCongr (G : (exceptionalCurve A).Modules) {a b : ℤ} (h : a = b) :
    curveTwist A G a ≅ curveTwist A G b :=
  twistModuleCongr (exceptionalCurve A) (curveTwistNegOne A) G (by rw [h])

/-- Twisting the clause-(1) isomorphism `ω_E ≅ ω_X|_E(-1)` by `n + 1` gives
`ω_X|_E(n) ≅ ω_E(n+1)`. -/
private theorem twist_pullback_dualizing_nonempty_iso {ωX : (blowUpScheme A).Modules}
    {ωE : (exceptionalCurve A).Modules}
    (e : ωE ≅ curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (-1))
    (n : ℤ) :
    Nonempty (curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) n ≅
      curveTwist A ωE (n + 1)) :=
  ⟨((tensorModulesMapIso (exceptionalCurve A) e (Iso.refl _) ≪≫
    curveTwistAddIso A _ (-1) (n + 1)) ≪≫
    curveTwistCongr _ (show (-1 : ℤ) + (n + 1) = n by ring)).symm⟩

/-- **The restriction of the dualizing module of the blowup to the exceptional curve is
`ω_E(1)`**, read off clause (1) of [Stacks, Tag 0B64] by twisting it once. -/
theorem nonempty_pullback_dualizing_iso_curveTwist {ωX : (blowUpScheme A).Modules}
    {ωE : (exceptionalCurve A).Modules}
    (e : ωE ≅ curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (-1)) :
    Nonempty ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX ≅
      curveTwist A ωE 1) :=
  (twist_pullback_dualizing_nonempty_iso e 0).map fun i => (curveTwistZeroIso A _).symm ≪≫ i

/-- **The twists of the restricted dualizing module are the twists of the dualizing sheaf of the
curve**, `ω_X|_E(n) ≅ ω_E(n+1)`: clause (1) of [Stacks, Tag 0B64], twisted. -/
theorem nonempty_pullback_curveTwist_iso {ωX : (blowUpScheme A).Modules}
    {ωE : (exceptionalCurve A).Modules}
    (e : ωE ≅ curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (-1))
    (n : ℤ) :
    Nonempty (curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) n ≅
      curveTwist A ωE (n + 1)) :=
  twist_pullback_dualizing_nonempty_iso e n

/-! ### Clause (2): vanishing of the first cohomology of the nonnegative twists -/

/-- **Vanishing of `Fⁿ` on the outer terms of a short exact sequence forces it in the middle.**
The first map is zero because its source is, so the second is a monomorphism, and a
monomorphism into a zero object has zero source. -/
private theorem isZero_deltaFunctor_middle {C D : Type*} [Category C] [Category D] [Abelian C]
    [Abelian D] (F : CategoryTheory.DeltaFunctor C D) {S : ShortComplex C} (hS : S.ShortExact)
    (n : ℕ) (h₁ : IsZero ((F.functor n).obj S.X₁)) (h₃ : IsZero ((F.functor n).obj S.X₃)) :
    IsZero ((F.functor n).obj S.X₂) := by
  have hf : (F.functor n).map S.f = 0 := h₁.eq_of_src _ _
  have hmono : Mono ((F.functor n).map S.g) :=
    (ShortComplex.exact_iff_mono (S.map (F.functor n)) hf).1 (F.exact_map hS n)
  have hg : (F.functor n).map S.g = 0 := h₃.eq_of_tgt _ _
  refine (IsZero.iff_id_eq_zero _).2 ?_
  have h0 : 𝟙 ((F.functor n).obj S.X₂) ≫ (F.functor n).map S.g =
      0 ≫ (F.functor n).map S.g := by rw [hg, comp_zero, zero_comp]
  exact (cancel_mono _).1 h0

/-- **Downward induction from an eventual value.** A predicate on the natural numbers which
holds above some bound and descends from `n + 1` to `n` holds everywhere. -/
private theorem forall_of_descends_of_eventually {P : ℕ → Prop} (hstep : ∀ n, P (n + 1) → P n)
    (h : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → P n) : ∀ n, P n := by
  obtain ⟨n₀, hn₀⟩ := h
  have key : ∀ k, P (n₀ - k) := by
    intro k
    induction k with
    | zero => simpa using hn₀ n₀ le_rfl
    | succ k ih =>
      by_cases hk : k < n₀
      · have heq : n₀ - k = n₀ - (k + 1) + 1 := by omega
        rw [heq] at ih
        exact hstep _ ih
      · simpa [Nat.sub_eq_zero_of_le (show n₀ ≤ k by omega),
          Nat.sub_eq_zero_of_le (show n₀ ≤ k + 1 by omega)] using ih
  intro n
  by_cases hn : n₀ ≤ n
  · exact hn₀ n hn
  · simpa [Nat.sub_sub_self (show n ≤ n₀ by omega)] using key (n₀ - n)

variable (A)

/-- `H¹(X, ω_X(n)) = 0` for every `n ≥ 0`, from the restriction sequence
`0 ⟶ ω_X(1) ⟶ ω_X ⟶ i_*(ω_X|_E) ⟶ 0`, the vanishing `H¹(E, ω_X|_E(n)) = 0` of `hcurve` and the
eventual vanishing `heventual`. -/
theorem isZero_firstCohomology_dualizingTwist (ωX : (blowUpScheme A).Modules)
    (f : schemeTwist A ωX 1 ⟶ ωX)
    (g : ωX ⟶ (Scheme.Modules.pushforward (exceptionalImmersion A)).obj
      ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX))
    (w : f ≫ g = 0) (hS : (ShortComplex.mk f g w).ShortExact)
    (hqc : ∀ n : ℕ, (curveTwist A
      ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (n : ℤ)).IsQuasicoherent)
    (hcurve : ∀ n : ℕ, IsZero (((cohomologyDeltaFunctor (exceptionalCurve A)).functor 1).obj
      (curveTwist A ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (n : ℤ))))
    (heventual : ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      IsZero (((cohomologyDeltaFunctor (blowUpScheme A)).functor 1).obj (schemeTwist A ωX n)))
    (n : ℕ) :
    IsZero (((cohomologyDeltaFunctor (blowUpScheme A)).functor 1).obj (schemeTwist A ωX n)) := by
  refine forall_of_descends_of_eventually (P := fun m =>
    IsZero (((cohomologyDeltaFunctor (blowUpScheme A)).functor 1).obj
      (schemeTwist A ωX m))) (fun m hm => ?_) heventual n
  have hSm := shortExact_twistedSequence (exceptionalImmersion A) (twistNegOne A) ωX
    ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) f g w hS (-(m : ℤ))
  refine isZero_deltaFunctor_middle (cohomologyDeltaFunctor (blowUpScheme A)) hSm 1 ?_ ?_
  · refine IsZero.of_iso hm (((cohomologyDeltaFunctor (blowUpScheme A)).functor 1).mapIso ?_)
    exact twistModuleCongr (blowUpScheme A) (twistNegOne A) ωX
      (show -(m : ℤ) - 1 = -((m : ℤ) + 1) by ring)
  · have := hqc m
    exact IsZero.of_iso (Functor.map_isZero
      (ModuleCat.restrictScalars (exceptionalImmersion A).appTop.hom) (hcurve m))
      (cohomologyHyperplaneIso (exceptionalImmersion A) (twistNegOne A)
        ((Scheme.Modules.pullback (exceptionalImmersion A)).obj ωX) (-(m : ℤ)) (hqc m) 1)

end AlgebraicGeometry.BlowUpDualizing

end
