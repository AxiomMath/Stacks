module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.FieldDescent
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.Integral
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.IrreducibleSeparableClosure
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.ProperGlobalSections
public import StacksFrontier.AlgebraicGeometry.Variety.Smooth.GeometricallyRegularNormal

/-!
# Smooth proper curves over a field (Stacks 0E81 and 0E83, part (2))

Let `X` be a scheme proper over a field `k` and let `k̄` be an algebraic closure of `k`. Part (2)
of Stacks 0E81 compares, for the classifying morphism of `X`, the following conditions on `X`:

* (b) `X` is smooth, `dim(X) = 1`, and `k = H⁰(X, 𝒪_X)`;
* (c) `X` is smooth, `dim(X) = 1`, and `X` is geometrically connected;
* (d) `X` is smooth, `dim(X) = 1`, and `X` is geometrically integral;
* (e) `X_{k̄}` is a smooth curve.

Part (2) of Stacks 0E83 adds to each of them that the genus is `g`. This file proves that these
conditions on `X` are equivalent.

## Main results

* `AlgebraicGeometry.geometricallyIrreducible_of_irreducibleSpace_pullback_isAlgClosure`: a
  scheme over `k` whose base change to an algebraic closure is irreducible is geometrically
  irreducible.
* `AlgebraicGeometry.smoothProperCurve_tfae`: conditions (b), (c), (d), (e) of Stacks 0E81,
  part (2), are equivalent.
* `AlgebraicGeometry.smoothProperCurveOfGenus_tfae`: conditions (b), (c), (d), (e) of
  Stacks 0E83, part (2), are equivalent.

## Implementation notes

A smooth scheme over a field is geometrically normal (Stacks 056T), so Stacks 0FD3 gives the
equivalence of (b), (c) and (d). For (d) and (e): smoothness passes to `X_{k̄}` by base change and
descends back by flat descent; the dimension and the genus do not change (Stacks 0BY9); and
`X_{k̄}` is integral when `X` is geometrically integral. Conversely, if `X_{k̄}` is irreducible, so
is its image `X_{k^{sep}}` for the separable closure `k^{sep}` of `k` in `k̄`, and `X` is
geometrically irreducible by Stacks 038I; being smooth, it is geometrically reduced.

## References

* [Stacks Project, Tag 0E81](https://stacks.math.columbia.edu/tag/0E81)
* [Stacks Project, Tag 0E83](https://stacks.math.columbia.edu/tag/0E83)
* [Stacks Project, Tag 0FD3](https://stacks.math.columbia.edu/tag/0FD3)
* [Stacks Project, Tag 056T](https://stacks.math.columbia.edu/tag/056T)
* [Stacks Project, Tag 038I](https://stacks.math.columbia.edu/tag/038I)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- A scheme over a field `k` whose base change to an algebraic closure of `k` is irreducible is
geometrically irreducible over `k`. -/
theorem geometricallyIrreducible_of_irreducibleSpace_pullback_isAlgClosure
    (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]
    [IrreducibleSpace ↥(pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))] :
    GeometricallyIrreducible f := by
  have : IsAlgClosed K := IsAlgClosure.isAlgClosed k
  let L := separableClosure k K
  let ιL : Spec (.of L) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k L))
  let φ : Spec (.of K) ⟶ Spec (.of L) := Spec.map (CommRingCat.ofHom (algebraMap L K))
  have hK : Spec.map (CommRingCat.ofHom (algebraMap k K)) = φ ≫ ιL := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  have hφ : Surjective φ := ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  have : IrreducibleSpace ↥(pullback f (φ ≫ ιL)) := hK ▸ inferInstance
  have hfst : Surjective (pullback.fst (pullback.snd f ιL) φ) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      (IsPullback.of_hasPullback (pullback.snd f ιL) φ).flip hφ
  let p := (pullbackLeftPullbackSndIso f ιL φ).inv ≫ pullback.fst (pullback.snd f ιL) φ
  have : IrreducibleSpace ↥(pullback f ιL) := p.surjective.irreducibleSpace p.continuous
  exact ((geometricallyIrreducible_tfae_of_isSepClosure k X f L).out 1 3).2 this

variable [IsProper f] (K : Type u) [Field K] [Algebra k K] [IsAlgClosure k K]

/-- **Stacks 0E81, part (2), conditions (b) to (e).** For a scheme `X` proper over a field `k`
and an algebraic closure `k̄` of `k`, the following are equivalent:
(b) `X` is smooth, `dim(X) = 1` and `k = H⁰(X, 𝒪_X)`;
(c) `X` is smooth, `dim(X) = 1` and `X` is geometrically connected;
(d) `X` is smooth, `dim(X) = 1` and `X` is geometrically integral;
(e) `X_{k̄}` is a smooth curve over `k̄`. -/
theorem smoothProperCurve_tfae :
    List.TFAE [
      Smooth f ∧ topologicalKrullDim X = 1 ∧ IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop),
      Smooth f ∧ topologicalKrullDim X = 1 ∧ GeometricallyConnected f,
      Smooth f ∧ topologicalKrullDim X = 1 ∧ GeometricallyIntegral f,
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        IsCurve K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))))] := by
  set ι : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have hdim : topologicalKrullDim ↥(pullback f ι) = topologicalKrullDim X :=
    topologicalKrullDim_baseChange k K (pullback.fst f ι) (pullback.snd f ι) f
      (IsPullback.of_hasPullback f ι)
  have h0FD3 (h : Smooth f) : List.TFAE [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop),
      GeometricallyConnected f, GeometricallyIrreducible f, GeometricallyIntegral f] :=
    isIso_globalSections_tfae_geometricallyConnected_irreducible_integral k f
      (have := h; isGeometricallyNormal_of_smooth f)
  tfae_have 1 ↔ 2 := and_congr_right fun h => and_congr_right fun _ => (h0FD3 h).out 1 2
  tfae_have 2 ↔ 3 := and_congr_right fun h => and_congr_right fun _ => (h0FD3 h).out 2 4
  tfae_have 3 → 4 := by
    rintro ⟨hsm, hd, hint⟩
    have : IsIntegral (pullback f ι) := (geometricallyIntegral_iff_isIntegral_pullback f).1 hint K
    have : IsVariety K (pullback.snd f ι) := ⟨⟩
    exact ⟨MorphismProperty.of_isPullback (P := @Smooth) (IsPullback.of_hasPullback f ι) hsm,
      (isCurve_iff K _).2 ⟨this, hdim.trans hd⟩⟩
  tfae_have 4 → 3 := by
    rintro ⟨hsm, hc⟩
    have hsmf : Smooth f := smooth_of_smooth_pullback_snd_spec_algebraMap k K f hsm
    refine ⟨hsmf, hdim.symm.trans hc.topologicalKrullDim_eq_one, ?_⟩
    have hnormal : IsGeometricallyNormal f := isGeometricallyNormal_of_smooth f
    have : GeometricallyReduced f :=
      (geometricallyReduced_iff_forall_isGeometricallyReducedAt f).2
        fun x K' _ _ x' hx' => (hnormal x K' x' hx').isReduced
    have : GeometricallyIrreducible f :=
      geometricallyIrreducible_of_irreducibleSpace_pullback_isAlgClosure k f K
    exact GeometricallyIntegral.of_geometricallyReduced_of_geometricallyIrreducible f
  tfae_finish

/-- **Stacks 0E83, part (2), conditions (b) to (e).** For a scheme `X` proper over a field `k`,
an algebraic closure `k̄` of `k` and `g ≥ 0`, the following are equivalent:
(b) `X` is smooth, `dim(X) = 1`, `k = H⁰(X, 𝒪_X)` and `X` has genus `g`;
(c) `X` is smooth, `dim(X) = 1`, `X` is geometrically connected and has genus `g`;
(d) `X` is smooth, `dim(X) = 1`, `X` is geometrically integral and has genus `g`;
(e) `X_{k̄}` is a smooth curve over `k̄` of genus `g`. -/
theorem smoothProperCurveOfGenus_tfae (g : ℕ) :
    List.TFAE [
      Smooth f ∧ topologicalKrullDim X = 1 ∧
        IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop) ∧ genus f = g,
      Smooth f ∧ topologicalKrullDim X = 1 ∧ GeometricallyConnected f ∧ genus f = g,
      Smooth f ∧ topologicalKrullDim X = 1 ∧ GeometricallyIntegral f ∧ genus f = g,
      Smooth (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        IsCurve K (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) ∧
        genus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) = g] := by
  have h := smoothProperCurve_tfae k f K
  have hg : genus (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) = genus f :=
    genus_baseChange k K (pullback.fst _ _) _ f (IsPullback.of_hasPullback _ _)
  have h12 := h.out 1 2
  have h23 := h.out 2 3
  have h34 := h.out 3 4
  tfae_have 1 ↔ 2 := by simpa only [and_assoc] using and_congr_left' (c := genus f = g) h12
  tfae_have 2 ↔ 3 := by simpa only [and_assoc] using and_congr_left' (c := genus f = g) h23
  tfae_have 3 ↔ 4 := by
    constructor
    · rintro ⟨hs, hd, hc, hgn⟩
      obtain ⟨hs', hc'⟩ := h34.1 ⟨hs, hd, hc⟩
      exact ⟨hs', hc', hg.trans hgn⟩
    · rintro ⟨hs', hc', hgn⟩
      obtain ⟨hs, hd, hc⟩ := h34.2 ⟨hs', hc'⟩
      exact ⟨hs, hd, hc, hg.symm.trans hgn⟩
  tfae_finish

end AlgebraicGeometry

end
