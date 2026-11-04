module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyPicardAmpleLocusField
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackFibered

/-!
# The smoothness half of Stacks 0DQ0, from smooth charts of the Picard stack and openness

`AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of_picard` asks for one thing through
every point of the base of a family of curves `X ⟶ T`: an object of the ample locus of
`Picardstack_{X/T}` over a smooth test scheme. The source's argument produces such an object in
three steps:
* **Surjectivity.** The ample locus has an object over the residue field of every point of `T`:
  `AlgebraicGeometry.CurveFamily.exists_picardObject_isInAmpleLocus_of_point`.
* **Smooth charts (Stacks 0D04 with 09DS, and 0DPJ).** `Picardstack_{X/T}` is algebraic and smooth
  over `T`. So for every field-valued object `A₀` of it there are a smooth `π : T' ⟶ T`, an object
  `A` over `T'`, and a field-valued point `y` of `T'` lying over the point of `A₀` after a field
  extension. Along `y`, the pullback of `A` is the pullback of `A₀`, so when `A₀` is in the ample
  locus so is the pullback of `A` along `y`. Ampleness is stable under base change
  (`AlgebraicGeometry.Space.isRelativelyAmple_baseChange`).
* **Openness of the ample locus (Stacks 0D3D).** If the pullback of `A` to a field-valued point `y`
  of `T'` is in the ample locus, then so is the pullback of `A` to an open neighbourhood `V ⊆ T'`
  of the image of `y`.

`AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of_picardCharts` takes the second and
third steps as the explicit inputs `hchart` and `hopen`, and proves the predicate. `hchart` states
the conclusion of the second step, ampleness of the pullback along `y`, directly, so that no
comparison of objects of the Picard stack is needed. The open `V ⟶ T'` followed by `π` is smooth,
and it hits the given point.

The third step, `hopen`, is Stacks 0D3D
(`AlgebraicGeometry.Space.exists_isOpenSubspace_factors_iff_isRelativelyAmple_of_isProper`);
`AlgebraicGeometry.CurveFamily.exists_isOpenImmersion_isInAmpleLocus_of_point` states it in the
shape used here.

## Main definitions

* `AlgebraicGeometry.CurveFamily.picardTestSchemeMap`: a morphism `g : T'' ⟶ T'` of the site,
  read as a morphism of test schemes from `g ≫ π` to `π`.

## Main results

* `AlgebraicGeometry.CurveFamily.isSmoothLocallyPolarized_of_picardCharts`.

## References

* [Stacks Project, Tag 0DQ0](https://stacks.math.columbia.edu/tag/0DQ0)
* [Stacks Project, Tag 0D04](https://stacks.math.columbia.edu/tag/0D04)
* [Stacks Project, Tag 0DPJ](https://stacks.math.columbia.edu/tag/0DPJ)
* [Stacks Project, Tag 0D3D](https://stacks.math.columbia.edu/tag/0D3D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A morphism `g : T'' ⟶ T'` of the site, read as a morphism of test schemes of the Picard
situation of a family of curves from `g ≫ π` to `π`. -/
def picardTestSchemeMap (X : CurveFamily B hZ) {T'' T' : BigFppfOver B integerBase hZ}
    (g : T'' ⟶ T') (π : T' ⟶ X.base) : X.picardTestScheme (g ≫ π) ⟶ X.picardTestScheme π :=
  CostructuredArrow.homMk g ((schemeSpaceFunctor B integerBase hZ).map_comp g π).symm

/-- **A family of curves is smooth locally polarized, given smooth charts of its Picard stack
and openness of the ample locus.** The two inputs:
* `hchart` (Stacks 0D04 with 09DS, and 0DPJ). For every object `A₀` of the ample locus over a
  field-valued point `x` of the base, it provides a smooth `π : T' ⟶ T`, an object `A` over `T'`,
  a field-valued point `y` of `T'` over `x` (through `e`), and the fact that the pullback of `A`
  along `y` is in the ample locus.
* `hopen` (Stacks 0D3D). If the pullback of an object `A` over `T'` along a field-valued point
  `y` is in the ample locus, then so is its pullback along an open immersion `V ⟶ T'` whose image
  contains that of `y`. This holds by
  `AlgebraicGeometry.CurveFamily.exists_isOpenImmersion_isInAmpleLocus_of_point`.
The surjectivity input is
`AlgebraicGeometry.CurveFamily.exists_picardObject_isInAmpleLocus_of_point`. -/
theorem isSmoothLocallyPolarized_of_picardCharts (X : CurveFamily B hZ)
    (hchart : ∀ (K : Type u) (_ : Field K) (hK : B.Contains (Spec (.of K)))
      (x : (schemeOverIntegers B).obj (B.obj hK) ⟶ X.base)
      (A₀ : Space.PicardObject X.picardSituation), A₀.T = X.picardTestScheme x →
        A₀.IsInAmpleLocus →
        ∃ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base),
          Smooth ((BigFppfOver.toScheme B integerBase hZ).map π) ∧
          ∃ (A : Space.PicardObject X.picardSituation) (hA : A.T = X.picardTestScheme π)
            (K' : Type u) (_ : Field K') (hK' : B.Contains (Spec (.of K')))
            (y : (schemeOverIntegers B).obj (B.obj hK') ⟶ T')
            (e : (schemeOverIntegers B).obj (B.obj hK') ⟶ (schemeOverIntegers B).obj (B.obj hK)),
            y ≫ π = e ≫ x ∧
            (Space.PicardSituation.pullbackObject A
              (X.picardTestSchemeMap y π ≫ eqToHom hA.symm)).IsInAmpleLocus)
    (hopen : ∀ (T' : BigFppfOver B integerBase hZ) (π : T' ⟶ X.base)
      (A : Space.PicardObject X.picardSituation) (hA : A.T = X.picardTestScheme π)
      (K' : Type u) (_ : Field K') (hK' : B.Contains (Spec (.of K')))
      (y : (schemeOverIntegers B).obj (B.obj hK') ⟶ T'),
      (Space.PicardSituation.pullbackObject A
          (X.picardTestSchemeMap y π ≫ eqToHom hA.symm)).IsInAmpleLocus →
        ∃ (V : BigFppfOver B integerBase hZ) (ι : V ⟶ T'),
          IsOpenImmersion ((BigFppfOver.toScheme B integerBase hZ).map ι) ∧
          Set.range ((BigFppfOver.toScheme B integerBase hZ).map y) ⊆
            Set.range ((BigFppfOver.toScheme B integerBase hZ).map ι) ∧
          (Space.PicardSituation.pullbackObject A
            (X.picardTestSchemeMap ι π ≫ eqToHom hA.symm)).IsInAmpleLocus) :
    X.IsSmoothLocallyPolarized := by
  refine isSmoothLocallyPolarized_of_picard X fun t => ?_
  obtain ⟨K, hKf, hK, x, ⟨p, hp⟩, A₀, hA₀, hamp₀⟩ :=
    exists_picardObject_isInAmpleLocus_of_point X t
  obtain ⟨T', π, hsm, A, hA, K', hK'f, hK', y, e, hyx, hampy⟩ := hchart K hKf hK x A₀ hA₀ hamp₀
  obtain ⟨V, ι, hι, hrange, hampV⟩ := hopen T' π A hA K' hK'f hK' y hampy
  let := hKf
  let := hK'f
  refine ⟨V, ι ≫ π, ?_, ?_, _, rfl, hampV⟩
  · rw [Functor.map_comp]
    infer_instance
  · have : Subsingleton (Spec (.of K)) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    obtain ⟨q⟩ : Nonempty (Spec (.of K')) := inferInstanceAs (Nonempty (PrimeSpectrum K'))
    obtain ⟨v, hv⟩ := hrange ⟨q, rfl⟩
    refine ⟨v, ?_⟩
    let F := BigFppfOver.toScheme B integerBase hZ
    have h1 : F.map π (F.map y q) = F.map x (F.map e q) := by
      have h := congrArg
        (fun φ : (schemeOverIntegers B).obj (B.obj hK') ⟶ X.base => F.map φ q) hyx
      simp only [Functor.map_comp] at h
      exact h
    change F.map π (F.map ι v) = t
    rw [hv, h1, ← hp]
    exact congrArg _ (@Subsingleton.elim (Spec (.of K)) inferInstance _ _)

end AlgebraicGeometry.CurveFamily

end
