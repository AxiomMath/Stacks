module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.ElementaryFibrationCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Comparison
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Picard.SmoothCurveLocalDimension
public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusAlphaPCoverSmooth
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.ConnectedFibres
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.BaseRestriction
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre

/-!
# Spreading out an elementary fibration from the generic fibre

Let `T` be a normal integral scheme, smooth over a field `k`, with generic point `η`, and let
`π : X̄ ⟶ T` be projective. Let `j : U ⟶ X̄` be an open immersion and `i : Z ⟶ X̄` a reduced
closed subscheme with support the complement of the image of `j`. Suppose that

* the generic fibre `X̄_η ⟶ Spec κ(η)` is smooth of relative dimension `1` and geometrically
  irreducible;
* `Z ⟶ T` is étale at every point of `Z` over `η`, and some point of `Z` lies over `η`.

Then there is an affine open `S₀ ∋ η` of `T` over which `U` is an elementary fibration.

## Main results

* `AlgebraicGeometry.isOpen_setOf_mem_smoothLocus_fiberDimensionAt_eq`: the points at which a
  morphism is smooth with fibre of dimension `n` form an open set.
* `AlgebraicGeometry.exists_isElementaryFibration_of_genericFibre`: the spreading out from the
  generic fibre.

## References

* SGA 4, Tome 3, Exposé XI, Proposition 3.3.
* [Stacks Project, Tag 02V4](https://stacks.math.columbia.edu/tag/02V4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-- The fibre dimension of a morphism is locally constant on its smooth locus: every point of the
smooth locus has an open neighbourhood on which the fibre dimension is constant. -/
theorem exists_open_forall_fiberDimensionAt_eq_of_mem_smoothLocus {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFinitePresentation f] {x : X} (hx : x ∈ f.smoothLocus) :
    ∃ (W : Set X) (n : ℕ), IsOpen W ∧ x ∈ W ∧ ∀ y ∈ W,
      topologicalKrullDimAt (f.fiber (f y)) (f.asFiber y) = (n : WithBot ℕ∞) := by
  have hsm : Smooth (f.smoothLocus.ι ≫ f) := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← Scheme.Hom.preimage_smoothLocus_eq]
    refine eq_top_iff.2 fun y _ => ?_
    change f.smoothLocus.ι y ∈ f.smoothLocus
    exact (Scheme.Opens.range_ι f.smoothLocus).le ⟨y, rfl⟩
  obtain ⟨V, hxV, n, hn⟩ := Smooth.exists_smoothOfRelativeDimension_nbhd (f.smoothLocus.ι ≫ f)
    ⟨x, hx⟩
  refine ⟨(V.ι ≫ f.smoothLocus.ι) '' Set.univ, n, ?_, ⟨⟨⟨x, hx⟩, hxV⟩, trivial, rfl⟩, ?_⟩
  · exact (V.ι ≫ f.smoothLocus.ι).isOpenEmbedding.isOpenMap _ isOpen_univ
  · rintro _ ⟨y, -, rfl⟩
    have h := fiberDimensionAt_eq_of_smoothOfRelativeDimension (V.ι ≫ f.smoothLocus.ι ≫ f) n y
    rw [← Category.assoc, fiberDimensionAt_comp_openImmersion] at h
    exact h

/-- The set of points at which `f` is smooth with fibre of dimension `n` is open. -/
theorem isOpen_setOf_mem_smoothLocus_fiberDimensionAt_eq {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (n : ℕ) :
    IsOpen {x : X | x ∈ f.smoothLocus ∧
      topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (n : WithBot ℕ∞)} := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨hx, hxn⟩
  obtain ⟨W, m, hW, hxW, hWm⟩ := exists_open_forall_fiberDimensionAt_eq_of_mem_smoothLocus f hx
  have hmn : (m : WithBot ℕ∞) = n := (hWm x hxW).symm.trans hxn
  refine ⟨W ∩ f.smoothLocus, fun y hy => ⟨hy.2, (hWm y hy.1).trans hmn⟩,
    hW.inter f.smoothLocus.isOpen, hxW, hx⟩

/-- If `a ≫ g = b ≫ S.ι` for an open `S` of the target, then `g` maps the image of `a` into `S`. -/
private theorem apply_mem_of_comp_eq_comp_ι {X Y T : Scheme.{u}} (S : T.Opens) (a : X ⟶ Y)
    (g : Y ⟶ T) (b : X ⟶ S.toScheme) (w : a ≫ g = b ≫ S.ι) (x : X) : g (a x) ∈ (S : Set T) := by
  rw [← Scheme.Hom.comp_apply, w, Scheme.Hom.comp_apply]
  exact (Scheme.Opens.range_ι S).le ⟨_, rfl⟩

/-- **Spreading out an elementary fibration from the generic fibre.** Let `T` be a normal
integral scheme, smooth over a field `k`, with generic point `η`, and let `π : X̄ ⟶ T` be
projective. Let `j : U ⟶ X̄` be an open immersion and `i : Z ⟶ X̄` a reduced closed subscheme
with support the complement of the image of `j`. If the generic fibre of `π` is smooth of
relative dimension `1` and geometrically irreducible, `Z ⟶ T` is étale at the points of `Z`
over `η`, and some point of `Z` lies over `η`, then there are an affine open `S₀ ∋ η` of `T`, the
open `U₀ = (j ≫ π)⁻¹(S₀)` of `U` and an elementary fibration `U₀ ⟶ S₀` lying over `j ≫ π`. -/
theorem exists_isElementaryFibration_of_genericFibre (k : Type u) [Field k]
    {T : Scheme.{u}} (τ : T ⟶ Spec (.of k)) [IsIntegral T] [IsNormal T] [Smooth τ]
    {Xt : Scheme.{u}} (π : Xt ⟶ T) (hπ : IsProjectiveMorphism π)
    (hsm : SmoothOfRelativeDimension 1 (π.fiberToSpecResidueField (genericPoint T)))
    (hgi : GeometricallyIrreducible (π.fiberToSpecResidueField (genericPoint T)))
    {U : Scheme.{u}} (j : U ⟶ Xt) [IsOpenImmersion j]
    {Z : Scheme.{u}} (i : Z ⟶ Xt) [IsClosedImmersion i] [IsReduced Z]
    (hZ : Set.range i.base = (Set.range j.base)ᶜ)
    (het : ∀ z : Z, π (i z) = genericPoint T → EtaleAt (i ≫ π) z)
    (hne : ∃ z : Z, π (i z) = genericPoint T) :
    ∃ (S₀ : T.Opens) (U₀ : Scheme.{u}) (e : U₀ ⟶ U) (f₀ : U₀ ⟶ S₀.toScheme),
      IsAffineOpen S₀ ∧ genericPoint T ∈ S₀ ∧ IsOpenImmersion e ∧ IsElementaryFibration f₀ ∧
        f₀ ≫ S₀.ι = e ≫ j ≫ π ∧ Set.range e.base = (j ≫ π).base ⁻¹' (S₀ : Set T) := by
  have : IsProper π := isProper_of_isProjectiveMorphism π hπ
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian τ
  have : IsIso (T.residue (genericPoint T)) := isIso_residue_genericPoint T
  have hflat : Flat (T.fromSpecResidueField (genericPoint T)) :=
    Stacks.AlgebraicGeometry.flat_fromSpecResidueField_of_isIso_residue _
  generalize hη : genericPoint T = η at hsm hgi het hne hflat
  have hG : ∀ x : Xt, π x = η → x ∈ π.smoothLocus ∧
      topologicalKrullDimAt (π.fiber (π x)) (π.asFiber x) = ((1 : ℕ) : WithBot ℕ∞) := by
    intro x hx
    cases hx
    have hsq := IsPullback.of_hasPullback π (T.fromSpecResidueField (π x))
    have : Smooth (pullback.snd π (T.fromSpecResidueField (π x))) :=
      @SmoothOfRelativeDimension.smooth 1 _ _ _ hsm
    have h := Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hsq (Or.inr hflat)
    rw [Scheme.Hom.smoothLocus_eq_top] at h
    refine ⟨?_, ?_⟩
    · have hy : π.asFiber x ∈ pullback.fst π (T.fromSpecResidueField (π x)) ⁻¹ᵁ π.smoothLocus :=
        h ▸ trivial
      have hy' : (pullback.fst π (T.fromSpecResidueField (π x))).base (π.asFiber x) ∈
          π.smoothLocus := hy
      have hx : (pullback.fst π (T.fromSpecResidueField (π x))).base (π.asFiber x) = x :=
        π.fiberι_asFiber x
      rwa [hx] at hy'
    · exact @topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field _ _ _ 1
        (π.fiberToSpecResidueField (π x)) hsm (π.asFiber x)
  let G := {x : Xt | x ∈ π.smoothLocus ∧
    topologicalKrullDimAt (π.fiber (π x)) (π.asFiber x) = ((1 : ℕ) : WithBot ℕ∞)}
  have hGo : IsOpen G := isOpen_setOf_mem_smoothLocus_fiberDimensionAt_eq π 1
  let E := {z : Z | EtaleAt (i ≫ π) z}
  have hEo : IsOpen E := isOpen_setOf_etaleAt (i ≫ π)
  have h₁ : IsClosed (π.base '' Gᶜ) := π.isClosedMap _ hGo.isClosed_compl
  have h₂ : IsClosed ((i ≫ π).base '' Eᶜ) := (i ≫ π).isClosedMap _ hEo.isClosed_compl
  have hη₁ : η ∉ π.base '' Gᶜ := by
    rintro ⟨x, hx, hxη⟩
    exact hx (hG x hxη)
  have hη₂ : η ∉ (i ≫ π).base '' Eᶜ := by
    rintro ⟨z, hz, hzη⟩
    exact hz (het z hzη)
  obtain ⟨S₀, hS₀, hηS₀, hS₀O⟩ : ∃ S₀ : T.Opens, IsAffineOpen S₀ ∧ η ∈ S₀ ∧
      (S₀ : Set T) ⊆ (π.base '' Gᶜ)ᶜ ∩ ((i ≫ π).base '' Eᶜ)ᶜ := by
    obtain ⟨_, ⟨S₀, hS₀, rfl⟩, hηS₀, hS₀O⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_inter hη₁ hη₂) (h₁.isOpen_compl.inter h₂.isOpen_compl)
    exact ⟨S₀, hS₀, hηS₀, hS₀O⟩
  have hgood : ∀ t ∈ (S₀ : Set T), t ∉ π.base '' Gᶜ ∧ t ∉ (i ≫ π).base '' Eᶜ :=
    fun t ht => hS₀O ht
  let ε := pullback.fst π S₀.ι
  let π₀ := pullback.snd π S₀.ι
  have hP : IsPullback ε π₀ π S₀.ι := IsPullback.of_hasPullback _ _
  have hεmem : ∀ x₀, π (ε x₀) ∈ (S₀ : Set T) := apply_mem_of_comp_eq_comp_ι S₀ ε π π₀ hP.w
  have hεG : ∀ x₀, ε x₀ ∈ G := fun x₀ => by
    by_contra h
    exact (hgood _ (hεmem x₀)).1 ⟨ε x₀, h, rfl⟩
  have : Smooth π₀ := by
    rw [← Scheme.Hom.smoothLocus_eq_top_iff,
      Scheme.Hom.smoothLocus_eq_preimage_of_isPullback hP (Or.inr inferInstance)]
    exact eq_top_iff.2 fun x₀ _ => (hεG x₀).1
  have : SmoothOfRelativeDimension 1 π₀ := by
    refine Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq π₀ 1 fun x₀ => ?_
    rw [fiberDimensionAt_eq_of_open_square ε π π₀ S₀.ι hP.w x₀]
    exact (hεG x₀).2
  have hπ₀ : IsProjectiveMorphism π₀ := hπ.baseChange S₀.ι
  have : Nonempty S₀ := ⟨⟨η, hηS₀⟩⟩
  have : IsAffine S₀.toScheme := hS₀
  have : IsIntegral S₀.toScheme := isIntegral_of_isOpenImmersion S₀.ι
  have : IsNormal S₀.toScheme := isNormal_of_isOpenImmersion S₀.ι
  have hy : S₀.ι (genericPoint S₀.toScheme) = η := hη ▸ Scheme.Opens.ι_genericPoint S₀
  have hgi₀ : GeometricallyIrreducible (π₀.fiberToSpecResidueField (genericPoint S₀.toScheme)) := by
    have hsq := isPullback_fiberToSpecResidueField_of_isPullback hP (genericPoint S₀.toScheme)
    have hgi' : GeometricallyIrreducible
        (π.fiberToSpecResidueField (S₀.ι (genericPoint S₀.toScheme))) := by
      rw [hy]; exact hgi
    exact MorphismProperty.of_isPullback hsq hgi'
  let ζ := pullback.fst i ε
  let i₀ := pullback.snd i ε
  have hQ : IsPullback ζ i₀ i ε := IsPullback.of_hasPullback _ _
  have hQP : IsPullback ζ (i₀ ≫ π₀) (i ≫ π) S₀.ι := hQ.paste_vert hP
  have : Etale (i₀ ≫ π₀) := by
    rw [etale_iff_forall_etaleAt]
    intro z₀
    rw [← etaleAt_iff_of_isPullback hQP (Or.inr inferInstance)]
    by_contra h
    exact (hgood _ (apply_mem_of_comp_eq_comp_ι S₀ ζ (i ≫ π) _ hQP.w z₀)).2 ⟨ζ z₀, h, rfl⟩
  have : Nonempty ↥(pullback i ε) := by
    obtain ⟨z, hz⟩ := hne
    have hz' : π.base (i.base z) ∈ Set.range S₀.ι.base := by
      rw [Scheme.Opens.range_ι, hz]; exact hηS₀
    obtain ⟨x₀, hx₀⟩ : i.base z ∈ Set.range ε.base := by
      rw [Scheme.Pullback.range_fst]; exact hz'
    obtain ⟨w, -, -⟩ := Scheme.Pullback.exists_preimage_pullback z x₀ hx₀.symm
    exact ⟨w⟩
  have : IsReduced (pullback i ε) := isReduced_of_isOpenImmersion ζ
  let e := pullback.fst j ε
  let j₀ := pullback.snd j ε
  have hR : IsPullback e j₀ j ε := IsPullback.of_hasPullback _ _
  have hrange : Set.range i₀.base = (Set.range j₀.base)ᶜ := by
    rw [Scheme.Pullback.range_snd, Scheme.Pullback.range_snd, hZ, Set.preimage_compl]
  have hfib := isElementaryFibration_of_smoothOfRelativeDimension_of_etale k (S₀.ι ≫ τ) π₀ hπ₀
    hgi₀ j₀ i₀ hrange
  refine ⟨S₀, pullback j ε, e, j₀ ≫ π₀, hS₀, hηS₀, inferInstance, hfib, ?_, ?_⟩
  · rw [Category.assoc, ← hP.w, ← Category.assoc, ← hR.w, Category.assoc]
  · rw [Scheme.Pullback.range_fst, Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    rfl

end AlgebraicGeometry

end
