module

public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.NodalContraction.CentreFibre
public import StacksFrontier.AlgebraicGeometry.NodalContraction.ExceptionalStalk
public import StacksFrontier.AlgebraicGeometry.NodalContraction.FibreReduced
public import StacksFrontier.AlgebraicGeometry.NodalContraction.FibreStalkQuotient
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Flat
public import StacksFrontier.AlgebraicGeometry.NodalContraction.GenericFibreField
public import StacksFrontier.AlgebraicGeometry.NodalContraction.SmoothAt
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPoint

/-!
# The contracted point: a uniformizer outside the square of the maximal ideal

Let `R` be a discrete valuation ring and `b : X ⟶ X'` a contraction of an exceptional curve with
centre `z`, where `X` is at-worst-nodal of relative dimension one over `Spec R` through
`f' : X' ⟶ Spec R` and `z` lies over the closed point of `Spec R`. A uniformizer of `R` maps
outside the square of the maximal ideal of the local ring of `X'` at `z`. If the local ring of
`X'` at `z` is regular of dimension two, the local ring of the closed fibre of `f'` at `z` is
regular of dimension one. If the local ring of the fibre of `b` at a point of the exceptional
curve is a field, the residue field of the closed fibre at `z` is geometrically reduced. Under
both conditions, a flat `f'` locally of finite presentation is smooth of relative dimension one
on a neighbourhood of `z`.

## Main results

* `AlgebraicGeometry.exists_span_maximalIdeal_and_notMem_sq`: the uniformizer of the base does
  not lie in the square of the maximal ideal at the contracted point.
* `AlgebraicGeometry.isField_stalk_closedFibre_of_isField_stalk_fiber`: the local ring of the
  closed fibre at a point of the exceptional curve is a field when the local ring of the fibre of
  the contraction there is.
* `AlgebraicGeometry.isRegularLocalRing_and_ringKrullDim_fiber_stalk_at_centre`: the local ring
  of the closed fibre at the contracted point is regular of dimension one.
* `AlgebraicGeometry.isGeometricallyReduced_residueField_fiber_at_centre`: the residue field of
  the closed fibre at the contracted point is geometrically reduced over the residue field of
  the base.
* `AlgebraicGeometry.exists_smoothOfRelativeDimension_nbhd_centre`: the base morphism is smooth
  of relative dimension one on a neighbourhood of the contracted point.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace IsLocalRing

universe u

namespace AlgebraicGeometry

/-- A point of the exceptional curve is mapped to the centre of the contraction. -/
private theorem map_subschemeι_eq_centre
    {X X' : Scheme.{u}} (D : X.IdealSheafData) (b : X ⟶ X') {z : X'} {hz : IsClosed ({z} : Set X')}
    (hDz : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).comap b)
    (x : D.subscheme) : b (D.subschemeι x) = z :=
  IsContractionOfExceptionalCurve.eq_centre_of_mem_support hDz
    (by rw [← D.range_subschemeι]; exact ⟨x, rfl⟩)

/-- Over a point mapping to the closed point, a nodal flat morphism has a uniformizer with nonzero
image in the stalk whose quotient by it is reduced. -/
private theorem exists_span_maximalIdeal_and_isReduced_quotient_span
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of R))
    (hg : IsAtWorstNodalOfRelativeDimensionOne g) (d : X) (hs : g d = closedPoint R) :
    ∃ π : (Spec (CommRingCat.of R)).presheaf.stalk (g d), π ≠ 0 ∧
      maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk (g d)) = Ideal.span {π} ∧
        (g.stalkMap d).hom π ≠ 0 ∧
          _root_.IsReduced (X.presheaf.stalk d ⧸ Ideal.span {(g.stalkMap d).hom π}) := by
  have : Flat g := flat hg.1.1
  obtain ⟨π, hπne, hπspan⟩ := exists_span_maximalIdeal_stalk_spec_of_eq_closedPoint R (g d) hs
  have hsclosed : IsClosed ({g d} : Set (Spec (CommRingCat.of R))) := by
    rw [hs]
    exact isClosed_singleton_closedPoint R
  refine ⟨π, hπne, hπspan, fun hzero => hπne (Flat.injective_stalkMap g d
    (hzero.trans (map_zero (g.stalkMap d).hom).symm)), ?_⟩
  have : IsReduced (g.fiber (g d)) := isReduced_fiber_of_nodal g hg (g d) ⟨g.asFiber d⟩
  have hJ : IdealSheafData.stalk ((Scheme.IdealSheafData.vanishingIdeal
      (⟨{g d}, hsclosed⟩ : Closeds (Spec (CommRingCat.of R)))).comap g) d =
      Ideal.span {(g.stalkMap d).hom π} := by
    rw [IdealSheafData.stalk_comap, IdealSheafData.stalk_vanishingIdeal_singleton (g d) hsclosed,
      hπspan, Stacks.Blowup.map_span_singleton]
  have := isReduced_quotient_stalk_comap_vanishingIdeal g (g d) hsclosed d
  rwa [hJ] at this

/-- **The uniformizer of the base does not lie in the square of the maximal ideal at the
contracted point.** The stalk of `Spec R` at `f' z` has a nonzero element `π` generating its
maximal ideal whose image in the local ring of `X'` at `z` does not lie in the square of the
maximal ideal. -/
public theorem exists_span_maximalIdeal_and_notMem_sq
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (f' : X' ⟶ Spec (CommRingCat.of R))
    (hf : IsAtWorstNodalOfRelativeDimensionOne (b ≫ f'))
    (z : X') (hz : IsClosed ({z} : Set X'))
    (hDz : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).comap b)
    (hs : f' z = closedPoint R) (x : D.subscheme) :
    ∃ π : (Spec (CommRingCat.of R)).presheaf.stalk (f' z), π ≠ 0 ∧
      maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk (f' z)) = Ideal.span {π} ∧
        (f'.stalkMap z).hom π ∉ maximalIdeal (X'.presheaf.stalk z) ^ 2 := by
  have hbz := map_subschemeι_eq_centre D b hDz x
  subst hbz
  set d : X := D.subschemeι x with hd
  obtain ⟨π, hπne, hπspan, hane, hredq⟩ :=
    exists_span_maximalIdeal_and_isReduced_quotient_span (b ≫ f') hf d hs
  refine ⟨π, hπne, hπspan, ?_⟩
  have hregd : IsRegularLocalRing (X.presheaf.stalk d) :=
    isRegularLocalRing_stalk_of_isContractionOfExceptionalCurve D b hb x
  have : IsDomain (X.presheaf.stalk d) := IsRegularLocalRing.isDomain (X.presheaf.stalk d)
  obtain ⟨t, htspan, htunit⟩ := exists_span_stalk_of_isContractionOfExceptionalCurve D b hb x
  have hmap : Ideal.map (b.stalkMap d).hom (maximalIdeal (X'.presheaf.stalk (b d))) ≤
      Ideal.span {t} := by
    rw [← htspan, idealSheafData_stalk_eq_map_maximalIdeal D b (b d) hz hDz x]
  have hφ : ((b ≫ f').stalkMap d).hom π =
      (b.stalkMap d).hom ((f'.stalkMap (b d)).hom π) := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  rw [hφ] at hane hredq
  exact notMem_sq_of_isReduced_quotient (b.stalkMap d).hom
    (maximalIdeal (X'.presheaf.stalk (b d))) t htunit hmap _ hane

/-- A reduced quotient of a Noetherian local domain with principal maximal ideal by a nonzero
nonunit is a field. -/
private theorem isField_quotient_of_principal_maximalIdeal
    {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    (hm : (maximalIdeal A).IsPrincipal)
    (a : A) (ha : a ≠ 0) (haunit : ¬ IsUnit a)
    [_root_.IsReduced (A ⧸ Ideal.span {a})] : IsField (A ⧸ Ideal.span {a}) := by
  have hne : Ideal.span {a} ≠ ⊥ := by simpa using ha
  obtain ⟨n, hn⟩ := exists_maximalIdeal_pow_eq_of_principal A hm (Ideal.span {a}) hne
  have hrad : (Ideal.span {a}).IsRadical :=
    (Ideal.isRadical_iff_quotient_reduced _).mpr inferInstance
  have hn0 : n ≠ 0 := by
    intro h
    subst n
    exact haunit (Ideal.span_singleton_eq_top.mp (by simpa using hn))
  have heq : Ideal.span {a} = maximalIdeal A := by
    calc
      _ = (Ideal.span {a}).radical := hrad.radical.symm
      _ = (maximalIdeal A).radical := by rw [hn, Ideal.radical_pow _ hn0]
      _ = _ := (maximalIdeal.isMaximal A).isPrime.radical
  exact (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp
    (heq ▸ maximalIdeal.isMaximal A)

/-- **The local ring of the closed fibre at a point of the exceptional curve is a field** when the
local ring of the fibre of the contraction there is. -/
public theorem isField_stalk_closedFibre_of_isField_stalk_fiber
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (f' : X' ⟶ Spec (CommRingCat.of R))
    (hf : IsAtWorstNodalOfRelativeDimensionOne (b ≫ f'))
    (z : X') (hz : IsClosed ({z} : Set X'))
    (hDz : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).comap b)
    (hs : f' z = closedPoint R) (x : D.subscheme)
    (hx : IsField ((b.fiber (b (D.subschemeι x))).presheaf.stalk
      (b.asFiber (D.subschemeι x)))) :
    IsField (((b ≫ f').fiber ((b ≫ f') (D.subschemeι x))).presheaf.stalk
      ((b ≫ f').asFiber (D.subschemeι x))) := by
  have hbz := map_subschemeι_eq_centre D b hDz x
  subst hbz
  set d : X := D.subschemeι x with hd
  obtain ⟨π, hπne, hπspan, hane, hredq⟩ :=
    exists_span_maximalIdeal_and_isReduced_quotient_span (b ≫ f') hf d hs
  have hregd : IsRegularLocalRing (X.presheaf.stalk d) :=
    isRegularLocalRing_stalk_of_isContractionOfExceptionalCurve D b hb x
  have : IsDomain (X.presheaf.stalk d) := IsRegularLocalRing.isDomain (X.presheaf.stalk d)
  obtain ⟨t, htspan, htunit⟩ := exists_span_stalk_of_isContractionOfExceptionalCurve D b hb x
  have hmaximal : (Ideal.map (b.stalkMap d).hom
      (maximalIdeal (X'.presheaf.stalk (b d)))).IsMaximal :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr
      ((quotientStalkEquivFiberStalk b d).isField hx)
  have hprincipal : (maximalIdeal (X.presheaf.stalk d)).IsPrincipal := by
    refine ⟨⟨t, ?_⟩⟩
    rw [Ideal.submodule_span_eq, ← htspan,
      idealSheafData_stalk_eq_map_maximalIdeal D b (b d) hz hDz x, eq_maximalIdeal hmaximal]
  have hmem : π ∈ maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk ((b ≫ f') d)) := by
    rw [hπspan]; exact Ideal.subset_span (Set.mem_singleton π)
  have haunit : ¬ IsUnit (((b ≫ f').stalkMap d).hom π) :=
    (mem_maximalIdeal _).mp
      (map_maximalIdeal_le ((b ≫ f').stalkMap d).hom (Ideal.mem_map_of_mem _ hmem))
  exact (fiberStalkEquivQuotientSpan (b ≫ f') d π hπspan).symm.isField
    (isField_quotient_of_principal_maximalIdeal hprincipal _ hane haunit)

/-- **The local ring of the closed fibre at the contracted point is regular of dimension one**,
when the local ring of `X'` at the contracted point is regular of dimension two. -/
public theorem isRegularLocalRing_and_ringKrullDim_fiber_stalk_at_centre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (f' : X' ⟶ Spec (CommRingCat.of R))
    (hf : IsAtWorstNodalOfRelativeDimensionOne (b ≫ f'))
    (z : X') (hz : IsClosed ({z} : Set X'))
    (hreg : IsRegularLocalRing (X'.presheaf.stalk z))
    (hdim : ringKrullDim (X'.presheaf.stalk z) = 2)
    (hDz : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).comap b)
    (hs : f' z = closedPoint R) (x : D.subscheme) :
    IsRegularLocalRing ((f'.fiber (f' z)).presheaf.stalk (f'.asFiber z)) ∧
      ringKrullDim ((f'.fiber (f' z)).presheaf.stalk (f'.asFiber z)) = 1 := by
  obtain ⟨π, hπne, hπspan, hπnot⟩ :=
    exists_span_maximalIdeal_and_notMem_sq D b hb f' hf z hz hDz hs x
  have := hreg
  have hmem : (f'.stalkMap z).hom π ∈ maximalIdeal (X'.presheaf.stalk z) := by
    refine map_maximalIdeal_le (f'.stalkMap z).hom (Ideal.mem_map_of_mem _ ?_)
    rw [hπspan]
    exact Ideal.subset_span (Set.mem_singleton π)
  obtain ⟨hregq, hdimq⟩ :=
    isRegularLocalRing_quotient_and_ringKrullDim_eq_one_of_notMem_sq hdim _ hmem hπnot
  have := hregq
  let eqv := fiberStalkEquivQuotientSpan f' z π hπspan
  refine ⟨IsRegularLocalRing.of_ringEquiv eqv, ?_⟩
  rwa [← eqv.ringKrullDim]

/-- **The residue field of the closed fibre at the contracted point is geometrically reduced over
the residue field of the base**, when the local ring of the fibre of the contraction at a point of
the exceptional curve is a field. -/
public theorem isGeometricallyReduced_residueField_fiber_at_centre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (f' : X' ⟶ Spec (CommRingCat.of R))
    (hf : IsAtWorstNodalOfRelativeDimensionOne (b ≫ f'))
    (z : X') (hz : IsClosed ({z} : Set X'))
    (hDz : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).comap b)
    (hs : f' z = closedPoint R) (x : D.subscheme)
    (hx : IsField ((b.fiber (b (D.subschemeι x))).presheaf.stalk
      (b.asFiber (D.subschemeι x)))) :
    letI κ := (Spec (CommRingCat.of R)).residueField (f' z)
    letI g := f'.fiberToSpecResidueField (f' z)
    letI : Algebra κ ((Spec (CommRingCat.of κ)).presheaf.stalk (g (f'.asFiber z))) :=
      StructureSheaf.stalkAlgebra κ (g (f'.asFiber z))
    letI : Algebra κ ((f'.fiber (f' z)).presheaf.stalk (f'.asFiber z)) :=
      ((g.stalkMap (f'.asFiber z)).hom.comp
        (algebraMap κ ((Spec (CommRingCat.of κ)).presheaf.stalk
          (g (f'.asFiber z))))).toAlgebra
    Algebra.IsGeometricallyReduced κ
      (ResidueField ((f'.fiber (f' z)).presheaf.stalk (f'.asFiber z))) := by
  have hbz := map_subschemeι_eq_centre D b hDz x
  subst hbz
  set d : X := D.subschemeι x with hd
  have hfield :=
    isField_stalk_closedFibre_of_isField_stalk_fiber D b hb f' hf (b d) hz hDz hs x hx
  let ν : (b ≫ f').fiber ((b ≫ f') d) ⟶ f'.fiber (f' (b d)) :=
    pullback.map _ _ _ _ b (𝟙 _) (𝟙 _) (by simp) (by simp)
  let g := f'.fiberToSpecResidueField (f' (b d))
  have hν : ν ≫ g = (b ≫ f').fiberToSpecResidueField ((b ≫ f') d) := by
    simp only [ν, g, Scheme.Hom.fiberToSpecResidueField, pullback.map]
    exact pullback.lift_snd _ _ _
  have hgr : GeometricallyReduced (ν ≫ g) := by
    rw [hν]
    exact geometricallyReduced_fiber_of_nodal (b ≫ f') hf ((b ≫ f') d)
      ⟨(b ≫ f').asFiber d⟩
  have h1 : ν ≫ f'.fiberι (f' (b d)) = (b ≫ f').fiberι ((b ≫ f') d) ≫ b :=
    pullback.lift_fst _ _ _
  have hp : ν ((b ≫ f').asFiber d) = f'.asFiber (b d) := by
    apply (f'.fiberι (f' (b d))).isEmbedding.injective
    calc
      f'.fiberι (f' (b d)) (ν ((b ≫ f').asFiber d)) =
          ((b ≫ f').fiberι ((b ≫ f') d) ≫ b) ((b ≫ f').asFiber d) :=
        (Scheme.Hom.comp_apply ν (f'.fiberι (f' (b d))) ((b ≫ f').asFiber d)).symm.trans
          (congrArg (fun q : (b ≫ f').fiber ((b ≫ f') d) ⟶ X' =>
            q ((b ≫ f').asFiber d)) h1)
      _ = b d := by
        rw [Scheme.Hom.comp_apply]
        exact congrArg b ((b ≫ f').fiberι_asFiber d)
      _ = f'.fiberι (f' (b d)) (f'.asFiber (b d)) := (f'.fiberι_asFiber (b d)).symm
  have hgeo := @isGeometricallyReduced_residueField_of_isField_stalk _ _ _ _ ν g hgr
    ((b ≫ f').asFiber d) hfield
  rwa [hp] at hgeo

/-- **The contraction is smooth of relative dimension one near the contracted point.** If `f'` is
flat and locally of finite presentation, the local ring of `X'` at `z` is regular of dimension
two, and the local ring of the fibre of `b` at a point of the exceptional curve is a field, then
`f'` is smooth of relative dimension one on an open neighbourhood of `z`. -/
public theorem exists_smoothOfRelativeDimension_nbhd_centre
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {X X' : Scheme.{u}} (D : X.IdealSheafData)
    (b : X ⟶ X') (hb : IsContractionOfExceptionalCurve D b)
    (f' : X' ⟶ Spec (CommRingCat.of R)) (hflat : Flat f')
    [LocallyOfFinitePresentation f']
    (hf : IsAtWorstNodalOfRelativeDimensionOne (b ≫ f'))
    (z : X') (hz : IsClosed ({z} : Set X'))
    (hreg : IsRegularLocalRing (X'.presheaf.stalk z))
    (hdim : ringKrullDim (X'.presheaf.stalk z) = 2)
    (hDz : D = (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds X')).comap b)
    (hs : f' z = closedPoint R) (x : D.subscheme)
    (hx : IsField ((b.fiber (b (D.subschemeι x))).presheaf.stalk
      (b.asFiber (D.subschemeι x)))) :
    ∃ V : X'.Opens, z ∈ V ∧ SmoothOfRelativeDimension 1 (V.ι ≫ f') := by
  obtain ⟨hregFibre, hdimFibre⟩ :=
    isRegularLocalRing_and_ringKrullDim_fiber_stalk_at_centre D b hb f' hf z hz hreg hdim
      hDz hs x
  have hgeo := isGeometricallyReduced_residueField_fiber_at_centre D b hb f' hf z hz hDz hs x hx
  have : LocallyOfFiniteType f' := inferInstance
  have hglft : LocallyOfFiniteType (f'.fiberToSpecResidueField (f' z)) :=
    AlgebraicGeometry.locallyOfFiniteType_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f'
        ((Spec (CommRingCat.of R)).fromSpecResidueField (f' z))) inferInstance
  have := hregFibre
  have hsmFibre : InfinitesimalLifting.SmoothAt
      (f'.fiberToSpecResidueField (f' z)) (f'.asFiber z) :=
    @smoothAt_of_isRegularLocalRing_of_isGeometricallyReduced_residueField
      _ _ _ (f'.fiberToSpecResidueField (f' z)) hglft (f'.asFiber z) hregFibre hgeo
  have hsm : InfinitesimalLifting.SmoothAt f' z :=
    smoothAt_of_flat_of_smoothAt_fiber f' hflat z hsmFibre
  have hyclosed : IsClosed ({f'.asFiber z} : Set (f'.fiber (f' z))) := by
    have hi : Function.Injective (f'.fiberι (f' z)) :=
      (f'.fiberι (f' z)).isEmbedding.injective
    have heq : (f'.fiberι (f' z)) ⁻¹' ({z} : Set X') = {f'.asFiber z} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => hi (h.trans (f'.fiberι_asFiber z).symm),
        fun h => h ▸ f'.fiberι_asFiber z⟩
    rw [← heq]
    exact hz.preimage (f'.fiberι (f' z)).continuous
  refine exists_smoothOfRelativeDimension_neighborhood_of_smoothAt f' z 1 hsm ?_
  rw [@AlgebraicGeometry.topologicalKrullDimAt_eq_krullDimOfRing_stalk
    _ _ (f'.fiber (f' z)) (f'.fiberToSpecResidueField (f' z)) hglft (f'.asFiber z) hyclosed]
  exact hdimFibre

end AlgebraicGeometry

end
