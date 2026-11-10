module

public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.GeneratorZeroScheme
public import StacksFrontier.AlgebraicGeometry.Variety.SmoothOverField.SmoothRationalPoint
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeOfCurve
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The divisor of a generator on a family of pointed curves

This is the claim in the proof of [Stacks, Tag 0B9X]. Let `k` be a field, `f : X ⟶ Spec k` a smooth
curve with a `k`-rational point, `T` a scheme over `k` and `f_T : X_T ⟶ T` the base change. For an
invertible `ℒ` on `X_T` with `Rf_{T,*}ℒ ≅ 𝒪_T[0]`, a generator `s : 𝒪_{X_T} ⟶ ℒ`
(`AlgebraicGeometry.PushforwardGenerator.IsGenerator`) is the adjunction section of the source
(where `𝒩 = 𝒪_T`), and its zero scheme is a relative effective Cartier divisor on `X_T / T`, finite
locally free over `T` when `f` is proper.

## Main results

* `AlgebraicGeometry.RigidifiedPicard.isIntegral_fiber_pullbackSnd`: the fibres of `f_T` are
  integral: they are base changes of `X` to fields, and `X` is geometrically integral
  ([Stacks, Tag 0CDW], [Stacks, Tag 020H] (3)).
* `AlgebraicGeometry.RigidifiedPicard.isRelativeEffectiveCartierDivisor_zeroScheme_of_isGenerator`:
  the zero scheme of a generator is a relative effective Cartier divisor, and finite locally free
  over `T` ([Stacks, Tag 0B9D]).

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 0B9D](https://stacks.math.columbia.edu/tag/0B9D)
* [Stacks Project, Tag 0CDW](https://stacks.math.columbia.edu/tag/0CDW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.RigidifiedPicard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  (σ : Spec (.of k) ⟶ X) (hσ : σ ≫ f = 𝟙 _)

include σ hσ in
/-- **The fibres of a base change of a smooth variety with a rational point are integral**: the
fibre of `X_T ⟶ T` over `v` is the base change of `X` to `κ(v)`, and `X` is geometrically
integral ([Stacks, Tag 0CDW]). -/
@[sga "3 XIX 2.1" "more general"]
theorem isIntegral_fiber_pullbackSnd [IsVariety k f] [Smooth f] {T : Scheme.{u}}
    (q : T ⟶ Spec (.of k)) (v : T) : IsIntegral ((pullback.snd f q).fiber v) := by
  let φ : Spec (T.residueField v) ⟶ Spec (.of k) := T.fromSpecResidueField v ≫ q
  let : Algebra k (T.residueField v) := (Spec.preimage φ).hom.toAlgebra
  have hφ : Spec.map (CommRingCat.ofHom (algebraMap k (T.residueField v))) = φ :=
    Spec.map_preimage φ
  have := (geometricallyIntegral_iff_isIntegral_pullback f).1
    (geometricallyIntegral_of_isVariety_of_smoothAt_rationalPoint f σ hσ
      (InfinitesimalLifting.smoothAt_of_smooth f _)) (T.residueField v)
  have hsq : IsPullback ((pullback.snd f q).fiberι v ≫ pullback.fst f q)
      ((pullback.snd f q).fiberToSpecResidueField v) f φ :=
    (IsPullback.of_hasPullback _ _).paste_horiz (IsPullback.of_hasPullback f q)
  exact IsIntegral.of_isIso (hφ ▸ hsq).isoPullback.inv

include σ hσ in
/-- **The claim of [Stacks, Tag 0B9X], for `𝒩 = 𝒪_T`**: the zero scheme `D` of a generator
`s : 𝒪_{X_T} ⟶ ℒ` relative to `f_T : X_T ⟶ T` is a relative effective Cartier divisor on
`X_T / T`, and `D ⟶ T` is finite locally free ([Stacks, Tag 0B9D], `f` proper). -/
theorem isRelativeEffectiveCartierDivisor_zeroScheme_of_isGenerator
    [IsCurve k f] [Smooth f] [IsProper f] {T : Scheme.{u}} (q : T ⟶ Spec (.of k))
    (L : (pullback f q).Modules)
    [SheafOfModules.IsInvertible (pullback f q).sheaf.obj (pullback f q).ringCatSheaf.property L]
    (s : SheafOfModules.unit (pullback f q).ringCatSheaf ⟶ L)
    (hs : PushforwardGenerator.IsGenerator (pullback.snd f q).toLRSHom.toShHom L s) :
    Stacks.Divisors.IsRelativeEffectiveCartierDivisor (pullback.snd f q)
        (zeroScheme (pullback f q) L ((L.unitHomEquiv s).eval (op ⊤))) ∧
      Stacks.Morphisms.IsFiniteLocallyFree
        ((zeroScheme (pullback f q) L ((L.unitHomEquiv s).eval (op ⊤))).subschemeι ≫
          pullback.snd f q) := by
  have hrel := PushforwardGenerator.isRelativeEffectiveCartierDivisor_zeroScheme_of_isGenerator L
    (pullback.snd f q) s hs (isIntegral_fiber_pullbackSnd f σ hσ q)
  refine ⟨hrel, ?_⟩
  have : SmoothOfRelativeDimension 1 (pullback.snd f q) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f q) (Stacks.Hilbert.smoothOfRelativeDimension_one_of_isCurve f)
  exact (isFiniteLocallyFree_iff_isRelativeEffectiveCartierDivisor_of_isProper _ _).2 hrel

end AlgebraicGeometry.RigidifiedPicard

end
