module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.GeometricallyNormalSmooth
public import StacksFrontier.AlgebraicGeometry.Curves.ModelNormalization
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChangeBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.NormalizationPurelyInseparable
public import StacksFrontier.AlgebraicGeometry.Variety.OneDimensional.NormalizationIso

/-!
# A smooth nonsingular projective model after a finite purely inseparable extension

Let `k` be a field and let `X` be a proper geometrically irreducible curve over `k`. There is a
finite purely inseparable extension `K/k` for which the nonsingular projective model of
`(X_K)_red` is smooth over `K`.

## Main results

* `AlgebraicGeometry.exists_isPurelyInseparable_smooth_nonsingularProjectiveModel`: Tag 0BY4(2)
  for a proper `X`, granted `h09NZ`.
* `AlgebraicGeometry.exists_isPurelyInseparable_smooth_nonsingularProjectiveModel'`: Tag 0BY4(2)
  for a proper `X`, with nothing carried.

## Implementation notes

Tag 0BXT produces the extension `K/k` together with geometric normality of the normalization of
the base change `pullback (Spec K ⟶ Spec k) sX`, whose structure morphism is the *first*
projection. The model of Tag 0BY4(1) is instead built from
`AlgebraicGeometry.reducedBaseChange`, the reduction of `pullback sX (Spec K ⟶ Spec k)`, whose
structure morphism is the *second* projection. The two are matched in three steps: the symmetry
isomorphism of the pullback, which is transported to the reductions by the functoriality
`AlgebraicGeometry.Scheme.reductionMap'`; the transport of the normalization along that
isomorphism, `AlgebraicGeometry.exists_iso_normalizationSchemeOverField_of_iso`; and
`AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_reduction` (Tag 035O), which identifies
the normalization of a scheme with that of its reduction. The resulting isomorphism of
normalizations over `Spec K` carries geometric normality across, and a geometrically normal
proper curve is smooth.

Two hypotheses are named rather than discharged. The hypothesis `h09NZ` is [Stacks, Tag 09NZ],
carried unchanged from the library's Tag 0A26 through Tag 0BY4(1). Properness of `X` is assumed:
the source deduces the general case from the projective one by replacing `X` by a nonsingular
projective model, which uses Theorem 0BY1, and that theorem is not in the library.

**`h09NZ` need not be carried**, and the primed
`exists_isPurelyInseparable_smooth_nonsingularProjectiveModel'`, which is where Tag 0BY4(2) is
registered, does not assume it: the model is `AlgebraicGeometry.normalizationModel'`, the
unconditional model of Tag 0BY4(1), whose projectivity is the step "a proper curve is projective"
applied to a normalization — integral of dimension one, where [Stacks, Tag 0A25] holds outright
from [Stacks, Tag 09ND]. Properness of `X` is still assumed there; that reduction is
carried out in
`AlgebraicGeometry.exists_isPurelyInseparable_smooth_nonsingularProjectiveModel_of_isCurve`. The
unprimed statement, which carries `h09NZ`, is kept unchanged.

## References

* [Stacks Project, Tag 0BY4](https://stacks.math.columbia.edu/tag/0BY4)
* [Stacks Project, Tag 0BXT](https://stacks.math.columbia.edu/tag/0BXT)
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
* [Stacks Project, Tag 0A25](https://stacks.math.columbia.edu/tag/0A25)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
* [Stacks Project, Tag 09NZ](https://stacks.math.columbia.edu/tag/09NZ)
* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
* [Stacks Project, Tag 0380](https://stacks.math.columbia.edu/tag/0380)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry

/-- The normalization of the reduced base change over `K` is geometrically normal, once that of
the first-projection base change is. -/
private theorem isGeometricallyNormal_normalizationOverField_reducedBaseChange
    (k k' : Type u) [Field k] [Field k'] [Algebra k k'] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [IsProper sX]
    (hgn : IsGeometricallyNormal
      (normalizationOverField k' (pullback.fst (spectrumMap k k') sX) ≫
        pullback.fst (spectrumMap k k') sX)) :
    IsGeometricallyNormal
      (normalizationOverField k' (reducedBaseChangeStructureMap k k' sX) ≫
        reducedBaseChangeStructureMap k k' sX) := by
  -- Instances for the two presentations of the base change and for their reductions.
  have hPp' : IsProper (pullback.fst (spectrumMap k k') sX) := inferInstance
  have hPi' : IsProper (pullback (spectrumMap k k') sX).nilradical.subschemeι := inferInstance
  have hLZ' : LocallyOfFiniteType
      ((pullback (spectrumMap k k') sX).nilradical.subschemeι ≫
        pullback.fst (spectrumMap k k') sX) :=
    IsProper.toLocallyOfFiniteType
  have hPp : IsProper (pullback.snd sX (spectrumMap k k')) := inferInstance
  have hPi : IsProper (pullback sX (spectrumMap k k')).nilradical.subschemeι := inferInstance
  have hLZ : LocallyOfFiniteType
      ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
        pullback.snd sX (spectrumMap k k')) :=
    IsProper.toLocallyOfFiniteType
  have hRed : IsReduced (pullback (spectrumMap k k') sX).nilradical.subscheme :=
    Scheme.isReduced_reduction _
  have hIsoHom : IsIso (pullbackSymmetry (spectrumMap k k') sX).hom := inferInstance
  have hIsoRed : IsIso (Scheme.reductionMap' (pullbackSymmetry (spectrumMap k k') sX).hom) :=
    inferInstance
  -- The symmetry of the pullback, read on the reductions.
  have hτ : (asIso (Scheme.reductionMap' (pullbackSymmetry (spectrumMap k k') sX).hom)).hom ≫
      ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
        pullback.snd sX (spectrumMap k k')) =
      (pullback (spectrumMap k k') sX).nilradical.subschemeι ≫
        pullback.fst (spectrumMap k k') sX := by
    change Scheme.reductionMap' (pullbackSymmetry (spectrumMap k k') sX).hom ≫
      ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
        pullback.snd sX (spectrumMap k k')) = _
    rw [Scheme.reductionMap'_comp_subschemeι_assoc, pullbackSymmetry_hom_comp_snd]
  -- Transport of the normalization along it.
  obtain ⟨ε, hε⟩ := exists_iso_normalizationSchemeOverField_of_iso k'
    ((pullback (spectrumMap k k') sX).nilradical.subschemeι ≫
      pullback.fst (spectrumMap k k') sX)
    ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
      pullback.snd sX (spectrumMap k k'))
    (asIso (Scheme.reductionMap' (pullbackSymmetry (spectrumMap k k') sX).hom)) hτ
  -- The normalization of the base change is the normalization of its reduction.
  obtain ⟨e', he'⟩ := Scheme.exists_normalizationScheme_iso_reduction
    (pullback (spectrumMap k k') sX)
    (finite_irreducibleComponents_of_locallyOfFiniteType k' (pullback.fst (spectrumMap k k') sX))
  have he'' : e'.hom ≫ normalizationOverField k'
        ((pullback (spectrumMap k k') sX).nilradical.subschemeι ≫
          pullback.fst (spectrumMap k k') sX) ≫
        (pullback (spectrumMap k k') sX).nilradical.subschemeι =
      normalizationOverField k' (pullback.fst (spectrumMap k k') sX) := he'
  have hchain : (e' ≪≫ ε).hom ≫
      normalizationOverField k'
          ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
            pullback.snd sX (spectrumMap k k')) ≫
        ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
          pullback.snd sX (spectrumMap k k')) =
      normalizationOverField k' (pullback.fst (spectrumMap k k') sX) ≫
        pullback.fst (spectrumMap k k') sX := by
    rw [Iso.trans_hom, Category.assoc, hε, ← he'']
    simp only [Category.assoc]
  exact
    isGeometricallyNormal_of_iso k' (e' ≪≫ ε).symm
      (normalizationOverField k' (pullback.fst (spectrumMap k k') sX) ≫
        pullback.fst (spectrumMap k k') sX) _
      ((Iso.inv_comp_eq _).2 hchain.symm) hgn

/-- **Stacks Project, Tag 0BY4, part (2).** Let `k` be a field and let `X` be a proper
geometrically irreducible curve over `k`. There is a finite purely inseparable extension `K/k`
for which `(X_K)_red` has a smooth nonsingular projective model.

The hypothesis `h09NZ` is [Stacks, Tag 09NZ], carried unchanged from Tag 0A26. -/
public theorem exists_isPurelyInseparable_smooth_nonsingularProjectiveModel
    (h09NZ : Stacks.HQuasiProjectiveDimensionOne.AmpleOfNoetherianSeparatedDimLEOne.{u})
    (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsCurve k sX] [GeometricallyIrreducible sX] [IsProper sX] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K)
      (_ : IsPurelyInseparable k K),
      ∃ M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
          (reducedBaseChangeStructureMap k K sX),
        Smooth M.structureMap := by
  obtain ⟨k', _, _, hfin, hpi, hgn⟩ :=
    exists_isPurelyInseparable_isGeometricallyNormal_normalization k sX
  refine ⟨k', inferInstance, inferInstance, hfin, hpi, ?_⟩
  refine ⟨normalizationModel h09NZ k' (reducedBaseChangeStructureMap k k' sX), ?_⟩
  have hCm : IsCurve k'
      (normalizationModel h09NZ k' (reducedBaseChangeStructureMap k k' sX)).structureMap :=
    (normalizationModel h09NZ k' (reducedBaseChangeStructureMap k k' sX)).isCurve
  have hPm : IsProper
      (normalizationModel h09NZ k' (reducedBaseChangeStructureMap k k' sX)).structureMap :=
    isProper_normalizationOverField_comp k' (reducedBaseChangeStructureMap k k' sX)
  exact smooth_of_isGeometricallyNormal_of_isCurve k' _
    (isGeometricallyNormal_normalizationOverField_reducedBaseChange k k' sX hgn)

/-- **Stacks Project, Tag 0BY4, part (2).** Let `k` be a field and let `X` be a proper
geometrically irreducible curve over `k`. There is a finite purely inseparable extension `K/k`
for which `(X_K)_red` has a smooth nonsingular projective model.

Nothing is carried; `X` is assumed proper. This is
`AlgebraicGeometry.exists_isPurelyInseparable_smooth_nonsingularProjectiveModel` with the
hypothesis `h09NZ` dropped, the model being the unconditional
`AlgebraicGeometry.normalizationModel'`. -/
@[stacks 0BY4 "part (2) for a proper `X`, with nothing carried: Tag 09NZ is not assumed, because \
the model is the normalization of `(X_K)_red`, integral of dimension one, where Tag 0A25 holds \
outright from Tag 09ND. One hypothesis is named: `X` is assumed proper, because the \
source's reduction of the general case to the projective case replaces `X` by a nonsingular \
projective model and so uses Theorem 0BY1; that reduction is carried out in \
`AlgebraicGeometry.exists_isPurelyInseparable_smooth_nonsingularProjectiveModel_of_isCurve`"]
public theorem exists_isPurelyInseparable_smooth_nonsingularProjectiveModel'
    (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsCurve k sX] [GeometricallyIrreducible sX] [IsProper sX] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K)
      (_ : IsPurelyInseparable k K),
      ∃ M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
          (reducedBaseChangeStructureMap k K sX),
        Smooth M.structureMap := by
  obtain ⟨k', _, _, hfin, hpi, hgn⟩ :=
    exists_isPurelyInseparable_isGeometricallyNormal_normalization k sX
  refine ⟨k', inferInstance, inferInstance, hfin, hpi, ?_⟩
  refine ⟨normalizationModel' k' (reducedBaseChangeStructureMap k k' sX), ?_⟩
  have hCm : IsCurve k'
      (normalizationModel' k' (reducedBaseChangeStructureMap k k' sX)).structureMap :=
    (normalizationModel' k' (reducedBaseChangeStructureMap k k' sX)).isCurve
  have hPm : IsProper
      (normalizationModel' k' (reducedBaseChangeStructureMap k k' sX)).structureMap :=
    isProper_normalizationOverField_comp k' (reducedBaseChangeStructureMap k k' sX)
  exact smooth_of_isGeometricallyNormal_of_isCurve k' _
    (isGeometricallyNormal_normalizationOverField_reducedBaseChange k k' sX hgn)

end AlgebraicGeometry

end
