module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Scheme.Glueing.ProjectiveLineSeparated

/-!
# The projective line over a domain is integral

The projective line over an integral domain `k` is an integral scheme. Reducedness is local, and
both charts are the spectrum of the domain `k[X]`. Irreducibility is the only point that uses
how the charts are glued: the first chart is a *dense* open, because the overlap
`Spec k[T, T⁻¹]` is a nonempty open of the irreducible second chart and hence dense in it, and
the overlap is contained in the first chart. A dense irreducible subset makes the whole space
irreducible.

## Main results

* `AlgebraicGeometry.denseRange_projectiveLineXChart`: the first chart of the projective line is
  dense.
* `AlgebraicGeometry.projectiveLine_irreducibleSpace`: the projective line over a domain is
  irreducible.
* `AlgebraicGeometry.projectiveLine_isReduced`: the projective line is reduced as soon as `k[X]`
  is reduced.
* `AlgebraicGeometry.projectiveLine_isIntegral`: the projective line over a domain is integral.

## Implementation notes

The inclusion of the overlap into the second chart is the map `k[X] ⟶ k[T, T⁻¹]`, `X ↦ T⁻¹`,
namely `AlgebraicGeometry.projectiveLineOverlapInverseCoordinate`; it is an open immersion
because it factors the localization map at `X` through the inversion isomorphism of the
punctured line. That it lands inside the first chart is the commuting square
`AlgebraicGeometry.isPullback_projectiveLineCharts`.

## References

* [Stacks Project, Tag 01JE](https://stacks.math.columbia.edu/tag/01JE)
-/

@[expose] public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [CommRing k]

/-- The inclusion of the overlap into the second chart of the projective line, namely `Spec` of
`k[X] ⟶ k[T, T⁻¹]`, `X ↦ T⁻¹`. -/
abbrev projectiveLineOverlapYInclusion :
    Spec (.of (LaurentPolynomial k)) ⟶ Spec (.of (Polynomial k)) :=
  Spec.map (CommRingCat.ofHom (projectiveLineOverlapInverseCoordinate k).toRingHom)

/-- The inclusion of the overlap into the second chart of the projective line is an open
immersion. -/
instance : IsOpenImmersion (projectiveLineOverlapYInclusion k) := by
  rw [show projectiveLineOverlapYInclusion k =
      (projectiveLineInversionIso k).hom ≫ projectiveLinePuncturedChart k from
    (projectiveLineInversionIso_hom_comp_puncturedChart k).symm]
  infer_instance

/-- The first chart of the projective line over a domain is dense. -/
theorem denseRange_projectiveLineXChart [IsDomain k] :
    Dense (Set.range (projectiveLineXChart k).base) := by
  have hdense : Dense (Set.range (projectiveLineOverlapYInclusion k).base) :=
    ((projectiveLineOverlapYInclusion k).isOpenEmbedding.isOpen_range).dense
      (Set.range_nonempty _)
  have hcomm : projectiveLinePuncturedChart k ≫ projectiveLineXChart k =
      projectiveLineOverlapYInclusion k ≫ projectiveLineYChart k :=
    (isPullback_projectiveLineCharts k).w
  have hsub : (projectiveLineYChart k).base ''
      (Set.range (projectiveLineOverlapYInclusion k).base) ⊆
      Set.range (projectiveLineXChart k).base := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    refine ⟨(projectiveLinePuncturedChart k).base z, ?_⟩
    calc (projectiveLineXChart k).base ((projectiveLinePuncturedChart k).base z)
        = (projectiveLinePuncturedChart k ≫ projectiveLineXChart k).base z := rfl
      _ = (projectiveLineOverlapYInclusion k ≫ projectiveLineYChart k).base z := by rw [hcomm]
      _ = (projectiveLineYChart k).base ((projectiveLineOverlapYInclusion k).base z) := rfl
  have hY : Set.range (projectiveLineYChart k).base ⊆
      closure ((projectiveLineYChart k).base ''
        Set.range (projectiveLineOverlapYInclusion k).base) := by
    rintro _ ⟨y, rfl⟩
    have h := (projectiveLineYChart k).isOpenEmbedding.isEmbedding
      |>.closure_eq_preimage_closure_image (Set.range (projectiveLineOverlapYInclusion k).base)
    rw [hdense.closure_eq] at h
    exact h.subset (Set.mem_univ y)
  refine dense_iff_closure_eq.mpr (Set.eq_univ_of_forall fun x ↦ ?_)
  obtain ⟨i, y, rfl⟩ := (projectiveLineGluingData k).ι_jointly_surjective x
  obtain ⟨i⟩ := i
  cases i
  · exact subset_closure ⟨y, rfl⟩
  · exact closure_mono hsub (hY ⟨y, rfl⟩)

/-- The projective line over a domain is irreducible. -/
@[ega "II 7.4.14" "partial"]
theorem projectiveLine_irreducibleSpace [IsDomain k] : IrreducibleSpace (projectiveLine k) := by
  have hpre : IsPreirreducible (Set.range (projectiveLineXChart k).base) := by
    rw [← Set.image_univ]
    exact (PreirreducibleSpace.isPreirreducible_univ
      (X := Spec (.of (Polynomial k)))).image _ (by fun_prop)
  have h1 : PreirreducibleSpace (projectiveLine k) := by
    refine ⟨?_⟩
    rw [← (denseRange_projectiveLineXChart k).closure_eq]
    exact hpre.closure
  exact { toNonempty := ⟨(projectiveLineXChart k).base (Classical.arbitrary _)⟩ }

/-- The projective line over `k` is reduced as soon as `k[X]` is reduced. -/
theorem projectiveLine_isReduced [_root_.IsReduced (Polynomial k)] :
    AlgebraicGeometry.IsReduced (projectiveLine k) := by
  have hred : ∀ i, AlgebraicGeometry.IsReduced ((projectiveLineGluingData k).openCover.X i) :=
    fun _ => inferInstanceAs (AlgebraicGeometry.IsReduced (Spec (.of (Polynomial k))))
  exact IsReduced.of_openCover (X := projectiveLine k) (projectiveLineGluingData k).openCover

/-- The projective line over a domain is an integral scheme. -/
@[ega "II 7.4.14" "more general"]
theorem projectiveLine_isIntegral [IsDomain k] :
    AlgebraicGeometry.IsIntegral (projectiveLine k) := by
  have _ : IrreducibleSpace (projectiveLine k) := projectiveLine_irreducibleSpace k
  have _ : AlgebraicGeometry.IsReduced (projectiveLine k) := projectiveLine_isReduced k
  exact isIntegral_of_irreducibleSpace_of_isReduced _

/-- The underlying space of the projective line over a domain is irreducible. -/
@[ega "II 7.4.14" "partial"]
instance projectiveLine_irreducibleSpace_inst [IsDomain k] :
    IrreducibleSpace (projectiveLine k) :=
  projectiveLine_irreducibleSpace k

/-- The projective line over a domain is an integral scheme. -/
@[ega "II 7.4.14" "more general"]
instance projectiveLine_isIntegral_inst [IsDomain k] :
    AlgebraicGeometry.IsIntegral (projectiveLine k) :=
  projectiveLine_isIntegral k

end AlgebraicGeometry

end

end
