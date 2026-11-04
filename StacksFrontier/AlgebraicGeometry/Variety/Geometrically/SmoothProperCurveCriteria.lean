module

public import Mathlib.FieldTheory.IsSepClosed
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Descent.SmoothFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ConnectedSeparableClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal

/-!
# Smooth proper curves over a field: five equivalent conditions

Let `X` be a proper scheme over a field `k`, with algebraic closure `k̄`. The following are
equivalent:

* `X` is smooth over `k`, `dim X = 1`, and `H⁰(X, 𝒪_X) = k`;
* `X` is smooth over `k`, `dim X = 1`, and `X` is geometrically connected;
* `X` is smooth over `k`, `dim X = 1`, and `X` is geometrically integral;
* `X_{k̄}` is a smooth curve over `k̄`.

These are conditions (2)(b)–(2)(e) of Stacks 0E81, and the argument is the one given there: a
smooth scheme over a field is geometrically normal (Stacks 056T), so Stacks 0FD3 gives the
equivalence of the first three; smoothness, properness and dimension pass to `X_{k̄}`, and back
by fpqc descent of smoothness (Stacks 02VL) and invariance of dimension under extension of the
ground field.

## Main results

* `AlgebraicGeometry.smooth_dimOne_tfae_geometricallyConnected_isCurve_algebraicClosure`: the
  four conditions are equivalent.

## Implementation notes

`H⁰(X, 𝒪_X) = k` is stated, as in
`AlgebraicGeometry.isIso_globalSections_iff_geometricallyConnected`, by the canonical homomorphism
`k → Γ(X, ⊤)` being an isomorphism. "`X_{k̄}` is a smooth curve" is `AlgebraicGeometry.IsCurve`
(Stacks 0A23: an integral scheme, separated and of finite type over `k̄`, of dimension one)
together with smoothness, for the base change `X ×_{Spec k} Spec k̄ → Spec k̄`, `k̄` being
Mathlib's `AlgebraicClosure k`.

The return from `X_{k̄}` to geometric connectedness of `X` goes through the separable closure
`k^{sep} ⊂ k̄` of `k` (Stacks 0387): `X_{k̄} → X_{k^{sep}}` is surjective, so `X_{k^{sep}}` is
connected when `X_{k̄}` is.

## References

* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 02VL](https://stacks.math.columbia.edu/tag/02VL)
* [Stacks Project, Tag 0387](https://stacks.math.columbia.edu/tag/0387)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- Connectedness of the base change of a scheme over `k` along `Spec K → Spec k` descends to the
base change along `Spec k' → Spec k` for an intermediate field `k ⊂ k' ⊂ K`: the projection
`X_K → X_{k'}` is surjective. -/
theorem connectedSpace_pullback_of_connectedSpace_pullback_comp (k' K : Type u) [Field k']
    [Field K] (g : Spec (.of k') ⟶ Spec (.of k)) (y : Spec (.of K) ⟶ Spec (.of k'))
    (h : ConnectedSpace ↥(pullback f (y ≫ g))) : ConnectedSpace ↥(pullback f g) := by
  have : ConnectedSpace ↥(pullback y (pullback.fst g f)) :=
    (pullbackRightPullbackFstIso g f y).schemeIsoToHomeo.connectedSpace_iff.mpr
      ((pullbackSymmetry f (y ≫ g)).schemeIsoToHomeo.connectedSpace_iff.mp h)
  exact (pullbackSymmetry g f).schemeIsoToHomeo.connectedSpace_iff.mp
    ((pullback.snd y (pullback.fst g f)).surjective.connectedSpace
      (pullback.snd y (pullback.fst g f)).continuous)

/-- A scheme over `k` is geometrically connected as soon as its base change to an algebraic
closure of `k` is connected (Stacks 0387, through the separable closure inside the algebraic
closure). -/
theorem geometricallyConnected_of_connectedSpace_pullback_algebraicClosure
    (h : ConnectedSpace ↥(pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))) :
    GeometricallyConnected f := by
  rw [geometricallyConnected_iff_connectedSpace_baseChange k (SeparableClosure k) f]
  refine connectedSpace_pullback_of_connectedSpace_pullback_comp k f (SeparableClosure k)
    (AlgebraicClosure k) _
    (Spec.map (CommRingCat.ofHom (algebraMap (SeparableClosure k) (AlgebraicClosure k)))) ?_
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap (SeparableClosure k) (AlgebraicClosure k)))
      ≫ Spec.map (CommRingCat.ofHom (algebraMap k (SeparableClosure k))) =
      Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  rwa [hcomp]

variable [IsProper f]

/-- **Stacks 0E81, the equivalence of conditions (2)(b)–(2)(e).** For a proper scheme `X` over a
field `k` the following are equivalent:

1. `X` is smooth over `k`, `dim X = 1`, and `H⁰(X, 𝒪_X) = k`;
2. `X` is smooth over `k`, `dim X = 1`, and `X` is geometrically connected;
3. `X` is smooth over `k`, `dim X = 1`, and `X` is geometrically integral;
4. `X_{k̄}` is a smooth curve over the algebraic closure `k̄` of `k`. -/
theorem smooth_dimOne_tfae_geometricallyConnected_isCurve_algebraicClosure :
    List.TFAE [
      Smooth f ∧ topologicalKrullDim X = 1 ∧ IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop),
      Smooth f ∧ topologicalKrullDim X = 1 ∧ GeometricallyConnected f,
      Smooth f ∧ topologicalKrullDim X = 1 ∧ GeometricallyIntegral f,
      IsCurve (AlgebraicClosure k) (pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k))))) ∧
        Smooth (pullback.snd f
          (Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))))] := by
  let g : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have hdim : topologicalKrullDim ↥(pullback f g) = topologicalKrullDim X :=
    topologicalKrullDim_baseChange k (AlgebraicClosure k) (pullback.fst f g) (pullback.snd f g) f
      (IsPullback.of_hasPullback f g)
  have h03 (hsm : Smooth f) : List.TFAE [
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop),
      GeometricallyConnected f,
      GeometricallyIrreducible f,
      GeometricallyIntegral f] := by
    have := hsm
    exact isIso_globalSections_tfae_geometricallyConnected_irreducible_integral k f
      (isGeometricallyNormal_of_smooth f)
  tfae_have 1 ↔ 2 := and_congr_right fun hs => and_congr_right fun _ => (h03 hs).out 1 2
  tfae_have 2 ↔ 3 := and_congr_right fun hs => and_congr_right fun _ => (h03 hs).out 2 4
  tfae_have 3 → 4 := by
    rintro ⟨hs, hd, hi⟩
    have := hs
    have := hi
    have : IsIntegral (pullback f g) :=
      GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd f g)
    have : IsVariety (AlgebraicClosure k) (pullback.snd f g) := IsVariety.mk
    exact ⟨(isCurve_iff _ _).mpr ⟨inferInstance, hdim.trans hd⟩, inferInstance⟩
  tfae_have 4 → 2 := by
    rintro ⟨hc, hs⟩
    refine ⟨?_, hdim.symm.trans hc.topologicalKrullDim_eq_one, ?_⟩
    · refine (MorphismProperty.IsLocalAtTarget.iff_of_forall_pullbackSnd (P := @Smooth)
        (K := Scheme.fpqcPrecoverage) (Scheme.Hom.singleton_mem_fpqcPrecoverage g)).mpr ?_
      rintro _ _ _ ⟨⟩
      exact hs
    · have : IsIntegral (pullback f g) := hc.toIsIntegral
      exact geometricallyConnected_of_connectedSpace_pullback_algebraicClosure k f inferInstance
  tfae_finish

end AlgebraicGeometry

end
