module

public import StacksFrontier.AlgebraicGeometry.Picard.HilbertAbelMap
public import StacksFrontier.AlgebraicGeometry.Picard.RelativeCurveDegreeBaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.DivisorDegreeTwist
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.AffineTarget

/-!
# The Abel map of a degree-`d` Hilbert family lands in degree `d`

Let `X ⟶ S` be smooth of relative dimension one and proper, with fibres of dimension at most one,
and let `Z` be a degree-`d` Hilbert family in `X` over an `S`-scheme `T`. The class
`γ_d(Z) = [𝒪_{X_T}(Z)]` of `Stacks.Hilbert.abelClass` has degree `d` on every fibre of
`X_T ⟶ T`. This is what makes the Abel map a map `Hilb^d_{X/S} ⟶ Pic^d_{X/S}`, clause (4) of
[Stacks, Tag 0BA0] at the level of functors of points.

## Main results

* `AlgebraicGeometry.invertibleCurveDegreeHom_schemePullbackClass_of_isIso` — the degree of a
  Picard class on a proper curve over a field is invariant under isomorphism over the field.
* `AlgebraicGeometry.invertibleCurveDegreeHom_picardClass_of_isFiniteLocallyFreeOfRank` — an
  effective Cartier divisor finite locally free of rank `d` over the field has degree `d`
  (`deg 𝒪_X(D) = deg D`, the rank-one case of [Stacks, Tag 0AYY]).
* `Stacks.Hilbert.relativeInvertibleDegreeHomAt_abelClass` — the Abel class of a degree-`d`
  family has degree `d` on the fibre over every point of the base.

## Implementation notes

For a point `t` of `T`, the family base changes along `Spec κ(t) ⟶ T`
(`Stacks.Hilbert.baseChange`) to a degree-`d` family over the field `κ(t)`, whose class is the
pullback of the class of `Z` (`Stacks.Hilbert.abelClass_baseChange`). The degree at `t` is the
degree at the unique point of `Spec κ(t)` of that pullback
(`AlgebraicGeometry.relativeInvertibleDegreeHomAt_schemePullbackClass_of_isPullback`), which is
the degree over `κ(t)`, which is `d` by the divisor-degree formula.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
* [Stacks Project, Tag 0AYY](https://stacks.math.columbia.edu/tag/0AYY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **The degree of a Picard class is invariant under isomorphism over the field.** If
`g' : X' ⟶ X` is an isomorphism of schemes proper of dimension at most one over `k`, compatible
with the structure morphisms, then pulling back along `g'` preserves the degree. -/
theorem invertibleCurveDegreeHom_schemePullbackClass_of_isIso (k : Type u) [Field k]
    {X' X : Scheme.{u}} (g' : X' ⟶ X) [IsIso g'] {f' : X' ⟶ Spec (.of k)}
    {f : X ⟶ Spec (.of k)} (w : g' ≫ f = f') [hf : IsProper f] [hf' : IsProper f']
    (hdim : topologicalKrullDim X ≤ 1) (hdim' : topologicalKrullDim X' ≤ 1)
    (x : Stacks.Picard.ofScheme X) :
    invertibleCurveDegreeHom k f' hdim' (Stacks.Picard.schemePullbackClass g' x) =
      invertibleCurveDegreeHom k f hdim x := by
  have hid : Spec.map (CommRingCat.ofHom (algebraMap k k)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id, Spec.map_id]
  have h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k))) := by
    rw [hid]
    exact IsPullback.of_horiz_isIso ⟨by rw [w, Category.comp_id]⟩
  exact invertibleCurveDegreeHom_schemePullbackClass_of_isPullback k k h hdim hdim' x

/-- **`deg 𝒪_X(D) = deg D` on Picard classes.** For `X` proper of dimension at most one over a
field `k` and an effective Cartier divisor `D` on `X` which is finite locally free of rank `d`
over `k`, the class of `𝒪_X(D)` has degree `d`. The rank-one case of the second assertion of
[Stacks, Tag 0AYY]. -/
theorem invertibleCurveDegreeHom_picardClass_of_isFiniteLocallyFreeOfRank (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    (D : X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor D] (d : ℕ)
    [Stacks.Morphisms.IsFiniteLocallyFreeOfRank (D.subschemeι ≫ f) d] :
    invertibleCurveDegreeHom k f hdim (Stacks.Divisors.picardClass D) = d := by
  rw [invertibleCurveDegreeHom_picardClass k f hdim (Stacks.Divisors.invertibleSheaf' _)
    (Stacks.Divisors.isInvertible_invertibleSheaf_picard _)]
  refine (invertibleCurveDegree_invertibleSheaf_eq_finrank_globalSections k f hdim D).trans ?_
  exact congrArg Nat.cast (finite_and_finrank_sections_of_isFiniteLocallyFreeOfRank
    (D.subschemeι ≫ f) d).2

end AlgebraicGeometry

namespace Stacks.Hilbert

variable {S : Scheme.{u}} {X : Over S} [SmoothOfRelativeDimension 1 X.hom] {d : ℕ}

/-- The `S`-scheme `Spec κ(t)` of a point `t` of an `S`-scheme `T`. -/
abbrev residueFieldOver (T : Over S) (t : T.left) : Over S :=
  Over.mk (T.left.fromSpecResidueField t ≫ T.hom)

/-- The morphism `Spec κ(t) ⟶ T` of `S`-schemes. -/
abbrev residueFieldOverHom (T : Over S) (t : T.left) : residueFieldOver T t ⟶ T :=
  Over.homMk (T.left.fromSpecResidueField t)

/-- **The Abel class of a degree-`d` Hilbert family has degree `d` on every fibre.** Let
`X ⟶ S` be smooth of relative dimension one, let `Z` be a degree-`d` family in `X` over `T`
and suppose `X_T ⟶ T` is proper with fibres of dimension at most one. Then the class
`[𝒪_{X_T}(Z)]` has degree `d` on the fibre of `X_T ⟶ T` over every point `t` of `T`. -/
theorem relativeInvertibleDegreeHomAt_abelClass {T : Over S} (Z : HilbertFamily X T d)
    [hπ : IsProper ((Over.pullback T.hom).obj X).hom]
    (hdim : ∀ t : T.left,
      topologicalKrullDim ↥(((Over.pullback T.hom).obj X).hom.fiber t) ≤ 1) (t : T.left) :
    relativeInvertibleDegreeHomAt ((Over.pullback T.hom).obj X).hom hdim t (abelClass Z) = d := by
  set g := residueFieldOverHom T t
  set π := ((Over.pullback T.hom).obj X).hom
  set π' := ((Over.pullback (residueFieldOver T t).hom).obj X).hom
  have hpb : IsPullback (familyBaseChangeMap X g) π' π (T.left.fromSpecResidueField t) :=
    isPullback_familyBaseChangeMap X g
  set c := hpb.isoPullback.hom
  have hc₁ : c ≫ π.fiberι t = familyBaseChangeMap X g := hpb.isoPullback_hom_fst
  have hc₂ : c ≫ π.fiberToSpecResidueField t = π' := hpb.isoPullback_hom_snd
  have : IsProper π' := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := @IsProper) hpb inferInstance
  have hdim' : topologicalKrullDim ((Over.pullback (residueFieldOver T t).hom).obj X).left ≤ 1 :=
    ((IsHomeomorph.topologicalKrullDim_eq c c.homeomorph.isHomeomorph).trans_le (hdim t))
  rw [relativeInvertibleDegreeHomAt_apply]
  refine (invertibleCurveDegreeHom_schemePullbackClass_of_isIso (T.left.residueField t) c hc₂
    (hf := isProper_fiberToSpecResidueField π t) (hdim t) hdim' _).symm.trans ?_
  refine (congrArg (invertibleCurveDegreeHom (T.left.residueField t) π' hdim')
    (((Stacks.Picard.schemePullbackClass_comp _ _ _).trans
      (congrArg (fun φ => Stacks.Picard.schemePullbackClass φ (abelClass Z)) hc₁)).trans
        (abelClass_baseChange g Z))).trans ?_
  have := (baseChange X g Z).isFiniteLocallyFreeOfRank
  exact invertibleCurveDegreeHom_picardClass_of_isFiniteLocallyFreeOfRank
    (T.left.residueField t) π' hdim' (baseChange X g Z).ideal d

end Stacks.Hilbert

end
