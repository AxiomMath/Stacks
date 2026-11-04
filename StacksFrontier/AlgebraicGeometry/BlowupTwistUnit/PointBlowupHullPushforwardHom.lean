module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PointBlowupHullPushforwardTwisted
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.PullbackHullComparisonHom

/-!
# The direct-image comparison at the blowup of a closed point, as a morphism

Let `W` be an integral regular Noetherian scheme of dimension two over `S ⟶ S₀`, let `w ∈ W` be
a closed point whose local ring is regular of dimension two and let `b : W' ⟶ W` be the blowing
up of `W` in the reduced point `{w}`. Write `L = (Ω^r_{W/S₀})^{**}` and
`L' = (Ω^r_{W'/S₀})^{**}`. This file constructs, with no hypothesis beyond the ones the dichotomy
of [Stacks, Tag 0B3T] carries, the canonical morphism

`Rb_*(L'[0]) ⟶ L[0]`   in `D_QCoh(𝒪_W)`.

## Main definitions

The elided prefix is `Stacks.BlowupTwistUnit`.

* `pullbackHullExterior`, `pullbackHullFormsObj`, `exceptionalTwistFunctor`: the modules
  `M = (⋀^r b^*Ω_{W/S₀})^{**}` and `b^*L` on `W'`, and the functor `𝒪_{W'}(E) ⊗ -` for `E` the
  exceptional divisor.
* `HullFormsPullbackBranch`: the dichotomy of [Stacks, Tag 0B3T] as data — an isomorphism of `L'`
  with `𝒪_{W'}(E) ⊗ M` or with `M`.
* `pushforwardHomOfTensorBranch'`, `pushforwardHomOfPullbackBranch'`: the morphism
  `Rb_*(L'[0]) ⟶ L[0]` on each branch.
* `pushforwardHomOfBranch`: the morphism from a branch witness.
* `pushforwardHom_hullForms`: **the morphism `Rb_*(L'[0]) ⟶ L[0]`, with no branch hypothesis.**

## Main results

* `nonempty_hullFormsPullbackBranch`: the dichotomy of [Stacks, Tag 0B3T], read as the
  nonemptiness of `Stacks.BlowupTwistUnit.HullFormsPullbackBranch`.
* `isQuasicoherent_pullbackHullFormsObj`, `isQuasicoherent_exceptionalTwistPullbackHullForms`:
  quasi-coherence of `b^*L` and of `𝒪_{W'}(E) ⊗ b^*L`.

## Implementation notes

`Nonempty (K ⟶ K')` is inhabited by the zero morphism for any pair of objects, so the morphism
`Stacks.BlowupTwistUnit.pushforwardHom_hullForms` is not chosen from a statement of that shape.
It is built from a witness of `Stacks.BlowupTwistUnit.HullFormsPullbackBranch`, a sum of two
isomorphism types, chosen from `Stacks.BlowupTwistUnit.nonempty_hullFormsPullbackBranch`; the
classical choice selects only which branch holds.

## References

* [Stacks Project, Tag 0B4T](https://stacks.math.columbia.edu/tag/0B4T)
* [Stacks Project, Tag 0B3T](https://stacks.math.columbia.edu/tag/0B3T)
* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Duality
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.BlowupTwistUnit

variable {S₀ S W : Scheme.{u}} [IsNoetherian W] [AlgebraicGeometry.IsIntegral W]

/-! ### The three modules the step compares -/

/-- `M = (⋀^r b^*Ω_{W/S₀})^{**}`, the reflexive hull of the top exterior power of the pullback of
the relative differentials. -/
abbrev pullbackHullExterior (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ) (w : W)
    (hw : IsClosed ({w} : Set W)) : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Modules :=
  reflexiveHull (Scheme.Modules.exteriorPower
    ((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
      (Scheme.Hom.relativeDifferentials (h ≫ p))) (r : ℤ))

/-- `b^*L = b^*((Ω^r_{W/S₀})^{**})`, the pullback of the determinant line bundle downstairs. -/
abbrev pullbackHullFormsObj (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ) (w : W)
    (hw : IsClosed ({w} : Set W)) : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Modules :=
  (Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
    (hullForms p (r : ℤ) h)

/-- The functor `𝒪_{W'}(E) ⊗ -` on `𝒪_{W'}-modules`, tensoring with the exceptional twist of the
blowing up. -/
abbrev exceptionalTwistFunctor (w : W) (hw : IsClosed ({w} : Set W)) :
    (AlgebraicGeometry.blowUp (pointIdeal w hw)).Modules ⥤
      (AlgebraicGeometry.blowUp (pointIdeal w hw)).Modules :=
  (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(AlgebraicGeometry.blowUp (pointIdeal w hw)).toRingedSpace.presheaf,
        (AlgebraicGeometry.blowUp (pointIdeal w hw)).toRingedSpace.IsSheaf⟩).obj
    (Stacks.Divisors.invertibleSheaf'
      (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)))

/-! ### Quasi-coherence of the two targets -/

/-- **`b^*((Ω^r_{W/S₀})^{**})` is quasi-coherent.** -/
theorem isQuasicoherent_pullbackHullFormsObj (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W ≤ 2) (w : W) (hw : IsClosed ({w} : Set W))
    (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (V : W.Opens) (hV : ∃ x : W, x ∈ V)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over V) r] :
    (pullbackHullFormsObj p h r w hw).IsQuasicoherent :=
  have := isInvertible_hullForms hreg hdim p h r V hV
  have := Stacks.Modules.isInvertible_pullback
    (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)) (hullForms p (r : ℤ) h)
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

omit [AlgebraicGeometry.IsNoetherian W] [AlgebraicGeometry.IsIntegral W] in
/-- **`𝒪_{W'}(E)` is quasi-coherent.** -/
theorem isQuasicoherent_exceptionalInvertibleSheaf (w : W) (hw : IsClosed ({w} : Set W)) :
    (show (AlgebraicGeometry.blowUp (pointIdeal w hw)).Modules from
      Stacks.Divisors.invertibleSheaf'
        (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw))).IsQuasicoherent :=
  have : Stacks.Divisors.IsEffectiveCartierDivisor
      (AlgebraicGeometry.exceptionalIdeal (pointIdeal w hw)) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _
  Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _

/-- **`𝒪_{W'}(E) ⊗ b^*((Ω^r_{W/S₀})^{**})` is quasi-coherent.** -/
theorem isQuasicoherent_exceptionalTwistPullbackHullForms
    (hreg : AlgebraicGeometry.IsRegular W) (hdim : topologicalKrullDim W ≤ 2)
    (w : W) (hw : IsClosed ({w} : Set W)) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (V : W.Opens) (hV : ∃ x : W, x ∈ V)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over V) r] :
    ((exceptionalTwistFunctor w hw).obj (pullbackHullFormsObj p h r w hw)).IsQuasicoherent :=
  have h1 := isQuasicoherent_exceptionalInvertibleSheaf w hw
  have h2 := isQuasicoherent_pullbackHullFormsObj hreg hdim w hw p h r V hV
  @AlgebraicGeometry.tensorSheaf_isQuasicoherent
    (AlgebraicGeometry.blowUp (pointIdeal w hw)).toRingedSpace _ _ h1 h2

/-! ### The dichotomy of Tag 0B3T as data -/

/-- **The dichotomy of [Stacks, Tag 0B3T] as data**: an isomorphism of `(Ω^r_{W'/S₀})^{**}` with
`𝒪_{W'}(E) ⊗ (⋀^r b^*Ω_{W/S₀})^{**}` or with `(⋀^r b^*Ω_{W/S₀})^{**}`. -/
abbrev HullFormsPullbackBranch (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ) (w : W)
    (hw : IsClosed ({w} : Set W)) : Type u :=
  ((exceptionalTwistFunctor w hw).obj (pullbackHullExterior p h r w hw) ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) ⊕
    (pullbackHullExterior p h r w hw ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h))

/-- **The dichotomy of [Stacks, Tag 0B3T]: `Stacks.BlowupTwistUnit.HullFormsPullbackBranch` is
nonempty.** -/
theorem nonempty_hullFormsPullbackBranch (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).IsCoherent]
    (U : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp (pointIdeal w hw), x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).over U) r] :
    Nonempty (HullFormsPullbackBranch p h r w hw) := by
  rcases nonempty_tensorIso_or_nonempty_iso_hullForms_vanishingIdeal_singleton'
    hreg hdim w hw hstalkdim p h r U hU with hd | hd
  · exact hd.elim fun d => ⟨Sum.inl d⟩
  · exact hd.elim fun d => ⟨Sum.inr d⟩

/-! ### The morphism on each branch -/

/-- **The direct-image comparison on the twisted branch**, as a morphism:

`Rb_*((Ω^r_{W'/S₀})^{**}[0]) ⟶ (Ω^r_{W/S₀})^{**}[0]`  in `D_QCoh(𝒪_W)`,

given the identification `d : 𝒪_{W'}(E) ⊗ (⋀^r b^*Ω_{W/S₀})^{**} ≅ (Ω^r_{W'/S₀})^{**}` that the
twisted branch of [Stacks, Tag 0B3T] supplies. -/
def pushforwardHomOfTensorBranch' (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (V : W.Opens) (hV : ∃ x : W, x ∈ V)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over V) r]
    (hqcohUp : (hullForms p (r : ℤ)
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)).IsQuasicoherent)
    (hqcoh : (hullForms p (r : ℤ) h).IsQuasicoherent)
    (d : (exceptionalTwistFunctor w hw).obj (pullbackHullExterior p h r w hw) ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) :
    (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent (hullForms p (r : ℤ)
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) hqcohUp 0) ⟶
      singleQuasiCoherent (hullForms p (r : ℤ) h) hqcoh 0 :=
  haveI := isInvertible_hullForms hreg hdim.le p h r V hV
  (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).map
      (singleQcohHom hqcohUp
        (isQuasicoherent_exceptionalTwistPullbackHullForms hreg hdim.le w hw p h r V hV)
        (d.inv ≫ (exceptionalTwistFunctor w hw).map
          (pullbackHullForms_hom p h hreg hdim w hw r V hV))) ≫
    (quasiCoherentDerivedPushforwardSingleIso hdim w hw _
      (isQuasicoherent_exceptionalTwistPullbackHullForms hreg hdim.le w hw p h r V hV)
      (isZeroFirstDirectImageBlowUp_exceptionalTwistPullback w hw hstalkdim
        (hullForms p (r : ℤ) h))
      (hullForms p (r : ℤ) h) hqcoh
      (pushforwardExceptionalTwistPullbackIso w hw hstalkdim (hullForms p (r : ℤ) h))).hom

/-- **The direct-image comparison on the untwisted branch**, as a morphism:

`Rb_*((Ω^r_{W'/S₀})^{**}[0]) ⟶ (Ω^r_{W/S₀})^{**}[0]`  in `D_QCoh(𝒪_W)`,

given the identification `d : (⋀^r b^*Ω_{W/S₀})^{**} ≅ (Ω^r_{W'/S₀})^{**}` that the untwisted
branch of [Stacks, Tag 0B3T] supplies. -/
def pushforwardHomOfPullbackBranch' (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (V : W.Opens) (hV : ∃ x : W, x ∈ V)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over V) r]
    (hqcohUp : (hullForms p (r : ℤ)
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)).IsQuasicoherent)
    (hqcoh : (hullForms p (r : ℤ) h).IsQuasicoherent)
    (d : pullbackHullExterior p h r w hw ≅
      hullForms p (r : ℤ) (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) :
    (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent (hullForms p (r : ℤ)
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) hqcohUp 0) ⟶
      singleQuasiCoherent (hullForms p (r : ℤ) h) hqcoh 0 :=
  haveI := isInvertible_hullForms hreg hdim.le p h r V hV
  (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
        (isQuasicoherent_homology_derivedPushforward_of_qcqs
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).map
      (singleQcohHom hqcohUp
        (isQuasicoherent_pullbackHullFormsObj hreg hdim.le w hw p h r V hV)
        (d.inv ≫ pullbackHullForms_hom p h hreg hdim w hw r V hV)) ≫
    (quasiCoherentDerivedPushforwardSingleIso hdim w hw _
      (isQuasicoherent_pullbackHullFormsObj hreg hdim.le w hw p h r V hV)
      (isZeroFirstDirectImageBlowUp_pullback w hw hstalkdim (hullForms p (r : ℤ) h))
      (hullForms p (r : ℤ) h) hqcoh
      (pushforwardPullbackIso hreg hdim w hw (hullForms p (r : ℤ) h))).hom

/-! ### The morphism, with no branch hypothesis -/

/-- **The direct-image comparison from a branch witness**: the morphism
`Rb_*((Ω^r_{W'/S₀})^{**}[0]) ⟶ (Ω^r_{W/S₀})^{**}[0]` built from an inhabitant of
`Stacks.BlowupTwistUnit.HullFormsPullbackBranch`, by
`Stacks.BlowupTwistUnit.pushforwardHomOfTensorBranch'` on the first summand and
`Stacks.BlowupTwistUnit.pushforwardHomOfPullbackBranch'` on the second. -/
def pushforwardHomOfBranch (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    [IsRegularLocalRing (W.presheaf.stalk w)]
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    (V : W.Opens) (hV : ∃ x : W, x ∈ V)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over V) r]
    (hqcohUp : (hullForms p (r : ℤ)
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)).IsQuasicoherent)
    (hqcoh : (hullForms p (r : ℤ) h).IsQuasicoherent)
    (branch : HullFormsPullbackBranch p h r w hw) :
    (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent (hullForms p (r : ℤ)
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) hqcohUp 0) ⟶
      singleQuasiCoherent (hullForms p (r : ℤ) h) hqcoh 0 :=
  match branch with
  | Sum.inl d =>
      pushforwardHomOfTensorBranch' hreg hdim w hw hstalkdim p h r V hV hqcohUp hqcoh d
  | Sum.inr d =>
      pushforwardHomOfPullbackBranch' hreg hdim w hw hstalkdim p h r V hV hqcohUp hqcoh d

/-- **`Rb_*((Ω^r_{W'/S₀})^{**}[0]) ⟶ (Ω^r_{W/S₀})^{**}[0]`, with no branch hypothesis**:
`Stacks.BlowupTwistUnit.pushforwardHomOfBranch` at a witness of
`Stacks.BlowupTwistUnit.HullFormsPullbackBranch` chosen from
`Stacks.BlowupTwistUnit.nonempty_hullFormsPullbackBranch`. -/
def pushforwardHom_hullForms (hreg : AlgebraicGeometry.IsRegular W)
    (hdim : topologicalKrullDim W = 2) (w : W) (hw : IsClosed ({w} : Set W))
    (hstalkdim : ringKrullDim (W.presheaf.stalk w) = 2) (p : S ⟶ S₀) (h : W ⟶ S) (r : ℕ)
    [(Scheme.Hom.relativeDifferentials (h ≫ p)).IsCoherent]
    [((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).IsCoherent]
    [(Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).IsCoherent]
    (U : (AlgebraicGeometry.blowUp (pointIdeal w hw)).Opens)
    (hU : ∃ x : AlgebraicGeometry.blowUp (pointIdeal w hw), x ∈ U)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (((Scheme.Modules.pullback (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))).obj
        (Scheme.Hom.relativeDifferentials (h ≫ p))).over U) r]
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials
        (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ (h ≫ p))).over U) r]
    (V : W.Opens) (hV : ∃ x : W, x ∈ V)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Hom.relativeDifferentials (h ≫ p)).over V) r]
    (hqcohUp : (hullForms p (r : ℤ)
      (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)).IsQuasicoherent)
    (hqcoh : (hullForms p (r : ℤ) h).IsQuasicoherent) :
    (quasiCoherentDerivedPushforward (AlgebraicGeometry.blowUpToBase (pointIdeal w hw))
          (isQuasicoherent_homology_derivedPushforward_of_qcqs
            (AlgebraicGeometry.blowUpToBase (pointIdeal w hw)))).obj
        (singleQuasiCoherent (hullForms p (r : ℤ)
          (AlgebraicGeometry.blowUpToBase (pointIdeal w hw) ≫ h)) hqcohUp 0) ⟶
      singleQuasiCoherent (hullForms p (r : ℤ) h) hqcoh 0 :=
  haveI : IsRegularLocalRing (W.presheaf.stalk w) := hreg.isRegularLocalRing_stalk w
  pushforwardHomOfBranch hreg hdim w hw hstalkdim p h r V hV hqcohUp hqcoh
    (nonempty_hullFormsPullbackBranch hreg hdim w hw hstalkdim p h r U hU).some

end Stacks.BlowupTwistUnit

end
