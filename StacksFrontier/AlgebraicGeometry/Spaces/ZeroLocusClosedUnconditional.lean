module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.QuasiSeparatedVeryReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.RelativeConditionComparisons
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.VeryReasonableImpliesReasonable
public import StacksFrontier.AlgebraicGeometry.Spaces.DevissageInputProof
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapZeroLocusLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Spaces.ZeroLocusClosedEtaleLocalDescent

/-!
# Stacks 0CWC, unconditionally

The two clauses of Stacks 0CWC — the vanishing locus of `u : ℱ ⟶ 𝒢` is a closed subspace of the
base, and of finite presentation over it when `ℱ` is of finite type — were stated in this
development with the dévissage `AlgebraicGeometry.Space.ModuleMapSituation.DevissageInput` as a
hypothesis.  That hypothesis is now a theorem,
`AlgebraicGeometry.Space.ModuleMapSituation.devissageInput`, and this file states both clauses at
the source's own hypotheses alone.

## Main results

* `AlgebraicGeometry.Space.isDecent_of_isFinitePresentation`: the footnote of Situation 0CV6.
* `AlgebraicGeometry.Space.ModuleMapSituation.fpTargetPrePureSituation`: the situation of
  Stacks 0CV6 attached to `𝒢` when `f` and `𝒢` are of finite presentation, with no further data.
* `AlgebraicGeometry.Space.ModuleMapSituation.isClosedSubspace_zeroSubfunctor_of_isPureRelative`.
* `ModuleMapSituation.isFinitePresentation_zeroSubfunctor_ι_of_isPureRelative`.

## References

* [Stacks Project, Tag 0CWC](https://stacks.math.columbia.edu/tag/0CWC)
-/

@[expose] public noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of algebraic spaces of finite presentation is decent: it is quasi-separated, and
quasi-separated morphisms are decent (Stacks 03M5).  This is the footnote of Situation 0CV6. -/
theorem isDecent_of_isFinitePresentation {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFinitePresentation B S hS f.hom) : IsDecent B S hS f.hom :=
  isDecent_of_isReasonable B S hS X.2 Y.2 f.hom
    (isReasonable_of_isVeryReasonable B S hS X.2 Y.2
      (isVeryReasonable_of_isQuasiSeparated B S hS X.2 Y.2 hf.2.2))

namespace ModuleMapSituation

/-- The purity situation of Stacks 0CV6 attached to a situation of Stacks 083F whose morphism and
target module are of finite presentation: the morphism is of finite type and decent, and the
module of finite type, because finite presentation gives all three. -/
abbrev fpTargetPrePureSituation {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G) (y : points B S hS D.Y.1) :
    PrePureSituation.{u, u} B S hS :=
  D.targetPrePureSituation (isFiniteType_of_isFinitePresentation B S hS hf)
    (isDecent_of_isFinitePresentation B S hS D.f hf)
    (SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite D.G) y

/-- **Stacks 0CWC, the closed-immersion clause.**  In Situation 083F, assume (1) `f` is of finite
presentation and (2) `𝒢` is of finite presentation, flat over the base and pure relative to it.
Then the vanishing locus of `u` is a closed subspace of the base.

The hypotheses are the source's, and only those: purity relative to the base is stated on the
situation of Stacks 0CV6 whose finite-type and decency conditions are *derived* from (1) and
(2) by `fpTargetPrePureSituation`, as the source does implicitly. -/
@[stacks 0CWC "closed immersion: the vanishing locus is a closed subspace of the base, at the \
source's hypotheses alone"]
theorem isClosedSubspace_zeroSubfunctor_of_isPureRelative (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hGflat : _root_.AlgebraicGeometry.Space.IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hpure : ∀ y : points B S hS D.Y.1, IsPureRelative (D.fpTargetPrePureSituation hf hGfp y)) :
    IsClosedSubspace B S hS D.zeroSubfunctor :=
  D.isClosedSubspace_zeroSubfunctor_of_devissage hf hGfp
    (SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite D.G) hGflat
    (isFiniteType_of_isFinitePresentation B S hS hf)
    (isDecent_of_isFinitePresentation B S hS D.f hf) hpure (devissageInput B S hS)

/-- **Stacks 0CWC, the finite-presentation clause.**  Under the hypotheses of
`isClosedSubspace_zeroSubfunctor_of_isPureRelative`, if moreover `ℱ` is of finite type, the
vanishing locus of `u` is of finite presentation over the base. -/
@[stacks 0CWC "finite presentation: the vanishing locus is of finite presentation over the base \
when the source module is of finite type, at the source's hypotheses alone"]
theorem isFinitePresentation_zeroSubfunctor_ι_of_isPureRelative
    (D : ModuleMapSituation.{u, u} B S hS)
    (hf : IsFinitePresentation B S hS D.f.hom)
    (hGfp : SheafOfModules.IsFinitePresentationOnSite D.G)
    (hGflat : _root_.AlgebraicGeometry.Space.IsFlatOver B S hS D.X.2 D.f.hom D.G)
    (hpure : ∀ y : points B S hS D.Y.1, IsPureRelative (D.fpTargetPrePureSituation hf hGfp y))
    (hFft : SheafOfModules.IsFiniteTypeOnSite D.F) :
    IsFinitePresentation B S hS D.zeroSubfunctor.ι :=
  D.isFinitePresentation_zeroSubfunctor_ι_of_devissage hf hGfp
    (SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite D.G) hGflat
    (isFiniteType_of_isFinitePresentation B S hS hf)
    (isDecent_of_isFinitePresentation B S hS D.f hf) hpure (devissageInput B S hS) hFft

end ModuleMapSituation

end AlgebraicGeometry.Space

end
