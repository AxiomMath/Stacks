module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosureImageValuativePoint
public import StacksFrontier.AlgebraicGeometry.Stacks.OpenSubmersiveComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.ValuativeSquareBaseChange

/-!
# The specialisation step for a valuative square of algebraic stacks

Let `f : 𝒳 ⟶ 𝒴` be a quasi-separated, universally closed 1-morphism of algebraic stacks over `S`
and let `q` be a valuative square for it, with valuation ring `A = q.R` and fraction field
`K = q.K`. Base changing `f` along the special point makes the generic point of the square into the
*generic section* `Spec K ⟶ Spec A ×_𝒴 𝒳`. The closure of the image of the generic section meets
the fibre over the *closed* point of `Spec A`, and there is a valuative square for the generic
section whose closed point maps to a point lying over the closed point of `Spec A`.

## Main results

* `AlgebraicGeometry.PrimeSpectrum.dense_range_comap_algebraMap`: the spectrum of a fraction field
  has dense image in the spectrum of the domain.
* `AlgebraicGeometry.Stack.ValuativeSquare.exists_point_over_closedPoint`: the closure of the image
  of the generic section contains a point lying over the closed point of `Spec A`.
* `AlgebraicGeometry.Stack.ValuativeSquare.exists_valuativeSquare_genericSection`: there is a
  valuative square for the generic section whose closed point maps to a point lying over the
  closed point of `Spec A`.

## References

* [Stacks Project, Tag 0CL2](https://stacks.math.columbia.edu/tag/0CL2)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0CLX](https://stacks.math.columbia.edu/tag/0CLX)
* [Stacks Project, Tag 0513](https://stacks.math.columbia.edu/tag/0513)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry

universe u w

attribute [local instance] AlgebraicGeometry.Stack.pointTopology

/-- The spectrum of a fraction field `K` of a domain `R` has dense image in the spectrum of `R`. -/
theorem PrimeSpectrum.dense_range_comap_algebraMap (R K : Type u) [CommRing R] [IsDomain R]
    [Field K] [Algebra R K] [IsFractionRing R K] :
    Dense (Set.range (PrimeSpectrum.comap (algebraMap R K))) := by
  have hbot : (⊥ : PrimeSpectrum R) ∈ Set.range (PrimeSpectrum.comap (algebraMap R K)) := by
    refine ⟨⊥, PrimeSpectrum.ext ?_⟩
    rw [PrimeSpectrum.comap_asIdeal]
    simp
  intro x
  have hgeneric : closure ({(⊥ : PrimeSpectrum R)} : Set (PrimeSpectrum R)) = Set.univ := by
    rw [PrimeSpectrum.closure_singleton]
    simp
  have hmono := closure_mono (Set.singleton_subset_iff.2 hbot)
  rw [hgeneric] at hmono
  exact hmono (Set.mem_univ x)

namespace Stack.ValuativeSquare

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ 𝒴}

/-- If `f` is universally closed then the closure of the image of the generic section of a
valuative square `q` for `f` contains a point lying over the *closed* point of `Spec A`. -/
theorem exists_point_over_closedPoint (q : ValuativeSquare B S hS f)
    (hclosed : AlgebraicStacks.UniversallyClosed B S hS f) :
    ∃ y, y ∈ closure (Set.range (pointsMap B S hS
            (genericStack.{u, w} B S hS q).val.val
            (genericStack.{u, w} B S hS q).val.property
            (baseChangeSquare.{u, w} B S hS q).pt.val.property
            (genericSection.{u, w} B S hS q).hom.hom)) ∧
      pointsHomeomorphScheme B S hS (siteObject B S hS q.ring_mem q.base)
          (pointsMap B S hS (baseChangeSquare.{u, w} B S hS q).pt.val.val
            (baseChangeSquare.{u, w} B S hS q).pt.val.property
            (specialStack.{u, w} B S hS q).val.property
            (baseChangeSquare.{u, w} B S hS q).fst.hom.hom y)
        = IsLocalRing.closedPoint q.R := by
  let instP := pointTopology B S hS (baseChangeSquare.{u, w} B S hS q).pt.val
  let instR := pointTopology B S hS
    (schemeFibredCategory B S hS (siteObject B S hS q.ring_mem q.base))
  let instK := pointTopology B S hS (schemeFibredCategory B S hS (siteObject B S hS q.field_mem
    (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)))
  set σ := pointsMap B S hS (genericStack.{u, w} B S hS q).val.val
      (genericStack.{u, w} B S hS q).val.property
      (baseChangeSquare.{u, w} B S hS q).pt.val.property
      (genericSection.{u, w} B S hS q).hom.hom with hσ
  set φ := pointsMap B S hS (baseChangeSquare.{u, w} B S hS q).pt.val.val
      (baseChangeSquare.{u, w} B S hS q).pt.val.property
      (specialStack.{u, w} B S hS q).val.property
      (baseChangeSquare.{u, w} B S hS q).fst.hom.hom with hφ
  set h := pointsHomeomorphScheme B S hS (siteObject B S hS q.ring_mem q.base) with hh
  set C := closure (Set.range σ) with hC
  have himg : IsClosed (φ '' C) :=
    isClosed_baseChange.{u, w} B S hS q hclosed C isClosed_closure
  have hcomp : pointsMap B S hS (genericStack.{u, w} B S hS q).val.val
      (genericStack.{u, w} B S hS q).val.property
      (specialStack.{u, w} B S hS q).val.property
      (leftMor.{u, w} B S hS q).hom.hom = φ ∘ σ := by
    rw [← genericSection_comp_fst.{u, w} B S hS q]
    exact AlgebraicStacks.pointsMap_comp' B S hS
      (genericSection.{u, w} B S hS q) (baseChangeSquare.{u, w} B S hS q).fst
  have hsub : Set.range (pointsMap B S hS (genericStack.{u, w} B S hS q).val.val
      (genericStack.{u, w} B S hS q).val.property
      (specialStack.{u, w} B S hS q).val.property
      (leftMor.{u, w} B S hS q).hom.hom) ⊆ φ '' C := by
    rw [hcomp]
    rintro _ ⟨z, rfl⟩
    exact ⟨σ z, subset_closure ⟨z, rfl⟩, rfl⟩
  have hnat : ∀ z, h (pointsMap B S hS (genericStack.{u, w} B S hS q).val.val
        (genericStack.{u, w} B S hS q).val.property
        (specialStack.{u, w} B S hS q).val.property
        (leftMor.{u, w} B S hS q).hom.hom z)
      = PrimeSpectrum.comap (algebraMap q.R q.K)
          (pointsHomeomorphScheme B S hS (siteObject B S hS q.field_mem
            (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base)) z) := by
    intro z
    rw [hh, leftMor_eq.{u, w} B S hS q]
    refine Eq.trans (pointsHomeomorphScheme_naturality B S hS q.genericMap _) ?_
    rw [show (BigFppfOver.toScheme B S hS).map q.genericMap
        = Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) from q.genericMap_left]
    exact Spec.map_apply _ _
  have hdense : Dense (h '' (φ '' C)) := by
    refine Dense.mono ?_ (PrimeSpectrum.dense_range_comap_algebraMap.{u} q.R q.K)
    rintro _ ⟨p, rfl⟩
    obtain ⟨z, rfl⟩ := (pointsHomeomorphScheme B S hS (siteObject B S hS q.field_mem
      (Spec.map (CommRingCat.ofHom (algebraMap q.R q.K)) ≫ q.base))).surjective p
    exact ⟨_, hsub ⟨z, rfl⟩, hnat z⟩
  have hall : h '' (φ '' C) = Set.univ := by
    have hclosedImage : IsClosed (h '' (φ '' C)) := h.isClosedMap _ himg
    rw [← hclosedImage.closure_eq, hdense.closure_eq]
  obtain ⟨p, hpmem, hpeq⟩ : IsLocalRing.closedPoint q.R ∈ h '' (φ '' C) := by
    rw [hall]
    exact Set.mem_univ _
  obtain ⟨y, hyC, hyeq⟩ := hpmem
  exact ⟨y, hyC, by rw [← hpeq, ← hyeq]⟩

/-- If `f` is quasi-separated and universally closed then, for any valuative square `q` for `f`,
there is a valuative square `q₂` for the *generic section* of `q` whose closed point maps to a
point of `Spec A ×_𝒴 𝒳` lying over the closed point of `Spec A`. -/
theorem exists_valuativeSquare_genericSection (q : ValuativeSquare B S hS f)
    (hqs : AlgebraicStacks.IsQuasiSeparated B S hS f)
    (hclosed : AlgebraicStacks.UniversallyClosed B S hS f) :
    ∃ (q₂ : ValuativeSquare B S hS (genericSection.{u, w} B S hS q))
      (hz : B.Contains
        (Spec (.of ((Spec (.of q₂.R)).residueField (IsLocalRing.closedPoint q₂.R))))),
      pointsHomeomorphScheme B S hS (siteObject B S hS q.ring_mem q.base)
          (pointsMap B S hS (baseChangeSquare.{u, w} B S hS q).pt.val.val
            (baseChangeSquare.{u, w} B S hS q).pt.val.property
            (specialStack.{u, w} B S hS q).val.property
            (baseChangeSquare.{u, w} B S hS q).fst.hom.hom
            (pointClass B S hS (baseChangeSquare.{u, w} B S hS q).pt.val.val
              (baseChangeSquare.{u, w} B S hS q).pt.val.property
              (fieldValuedPointMap B S hS
                (schemeFibredCategory B S hS (siteObject B S hS q₂.ring_mem q₂.base)).val
                q₂.y.hom
                (closedPointFieldValuedPoint B S hS
                  (siteObject B S hS q₂.ring_mem q₂.base)
                  (IsLocalRing.closedPoint q₂.R) hz))))
        = IsLocalRing.closedPoint q.R := by
  obtain ⟨y, hyC, hyeq⟩ := exists_point_over_closedPoint.{u, w} B S hS q hclosed
  obtain ⟨q₂, hz, hq₂⟩ := exists_valuationRing_of_mem_closure_range_pointsMap B S hS
    (genericSection.{u, w} B S hS q)
    (isQuasiCompactMorphism_genericSection.{u, w} B S hS q hqs) y hyC
  exact ⟨q₂, hz, by rw [hq₂]; exact hyeq⟩

end Stack.ValuativeSquare

end AlgebraicGeometry

end
