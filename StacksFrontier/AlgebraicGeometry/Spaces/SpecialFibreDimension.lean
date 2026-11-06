module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FibreDimension.AffineFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.CodimensionZeroPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.CodimensionZeroCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FieldFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Fibres.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperModificationSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionBaseChange
public import StacksFrontier.RingTheory.SpecialFibreDimension
public import StacksFrontier.Topology.Irreducible.GenericPoints

/-!
# The special fibre of a generically finite algebraic space over a local domain

Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension at least one and let `f : X → Spec A`
be a morphism of algebraic spaces which is locally of finite type and generically finite, in
the sense that the points of `|X|` over the generic point of `Spec A` are the generic points of
the irreducible components of `|X|`. Then the special fibre `X_κ` has dimension at most
`dim(A) - 1`.

## Main definitions

* `AlgebraicGeometry.Space.residueFieldPoint` is the closed point of `Spec A`, for `A` local,
  read as a point of the base valued in the residue field; the special fibre of an algebraic
  space over `Spec A` is the field fibre over it.

## Main results

* `AlgebraicGeometry.topologicalKrullDimAt_fiber_add_one_le_ringKrullDim` is the bound for an
  affine scheme of finite type over `Spec A`.
* `AlgebraicGeometry.Space.dimension_fieldFibre_add_one_le_ringKrullDim` is the bound for a
  decent algebraic space, and
  `AlgebraicGeometry.Space.dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralSpace` the
  bound for an integral one with a single point over the generic point of the base.
* `AlgebraicGeometry.mem_genericPoints_spec_iff`: a point of the spectrum of a ring is a
  generic point of an irreducible component exactly when it is a minimal prime.

## Implementation notes

The bound lives in `WithBot ℕ∞`, the codomain of the dimension of an algebraic space, where the
source's `dim ≤ dim(A) - 1` has to be written `dim + 1 ≤ dim(A)` for want of subtraction.

The space-level bound is proved one point of `X_κ` at a time. Base change along the closed
point, Tag 04NS, identifies the dimension of `X_κ` at a point with the relative dimension of
`f` at the point of `|X|` below it, which only needs `f` locally of finite type; an affine
étale chart then reads that relative dimension off the fibre of an affine scheme of finite type
over `Spec A`, by the chart equation of Tag 04NM. The generic hypothesis is transported to that
chart through Tags 0ABV and 0BAQ, and becomes the hypothesis of the commutative-algebra bound
`ringKrullDim_quotient_map_maximalIdeal_add_one_le`.

Presenting the affine chart as the spectrum of a ring is the only step that leaves the language
of schemes: the chart is isomorphic to `Spec Γ(W, ⊤)`, that isomorphism is étale and so
preserves the local dimension of a fibre, and it matches up generic points with minimal primes.

The reduction of the integral case to the decent one needs a generic point of `|X|` to exist,
which comes from the density of the points of codimension zero, Tag 0BAR, rather than from
sobriety of the point space.

## References

* [Stacks Project, Tag 0AYJ](https://stacks.math.columbia.edu/tag/0AYJ)
* [Stacks Project, Tag 0ABV](https://stacks.math.columbia.edu/tag/0ABV)
* [Stacks Project, Tag 0BAQ](https://stacks.math.columbia.edu/tag/0BAQ)
* [Stacks Project, Tag 0BAR](https://stacks.math.columbia.edu/tag/0BAR)
* [Stacks Project, Tag 04NM](https://stacks.math.columbia.edu/tag/04NM)
* [Stacks Project, Tag 04NS](https://stacks.math.columbia.edu/tag/04NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- In `WithBot ℕ∞` a bound on every member of a family after adding one bounds the supremum
after adding one. -/
private theorem iSup_add_one_le {ι : Sort*} {d : ι → WithBot ℕ∞} {c : WithBot ℕ∞}
    (h : ∀ i, d i + 1 ≤ c) : (⨆ i, d i) + 1 ≤ c := by
  rcases eq_or_ne c ⊤ with rfl | hc
  · exact le_top
  have hb : c ≤ 0 → ∀ i, d i = ⊥ := fun hc i ↦ by
    cases hd : d i with
    | bot => rfl
    | coe n => simpa [hd] using (h i).trans hc
  by_cases hc0 : c ≤ 0
  · simp [hb hc0]
  obtain ⟨m, hm⟩ := WithBot.ne_bot_iff_exists.mp fun h' ↦ hc0 (h'.le.trans bot_le)
  have hm' : m ≠ ⊤ := by rintro rfl; exact hc hm.symm
  obtain ⟨k, rfl⟩ := ENat.ne_top_iff_exists.mp hm'
  subst hm
  match k with
  | 0 => simp at hc0
  | (j + 1) =>
      have hle : ∀ i, d i ≤ ((j : ℕ) : WithBot ℕ∞) := fun i ↦ by
        have hi : d i + 1 ≤ ((j + 1 : ℕ) : WithBot ℕ∞) := by exact_mod_cast h i
        have h1 : d i < ((j + 1 : ℕ) : WithBot ℕ∞) := ENat.WithBot.add_one_le_natCast_iff.mp hi
        rw [Nat.cast_add_one] at h1
        exact ENat.WithBot.lt_add_one_iff.mp h1
      calc (⨆ i, d i) + 1 ≤ ((j : ℕ) : WithBot ℕ∞) + 1 := by gcongr; exact iSup_le hle
        _ = _ := by push_cast; ring

/-- A point of the spectrum of a ring is a generic point of an irreducible component exactly
when the prime naming it is a minimal prime. -/
theorem mem_genericPoints_spec_iff (R : Type u) [CommRing R] (x : PrimeSpectrum R) :
    x ∈ genericPoints (Spec (.of R)) ↔ x.asIdeal ∈ minimalPrimes R := by
  rw [show (x ∈ genericPoints (Spec (CommRingCat.of R))) ↔
      (x ∈ genericPoints (PrimeSpectrum R)) from Iff.rfl]
  rw [genericPoints, Set.mem_ofPred_eq, ← PrimeSpectrum.vanishingIdeal_singleton,
    PrimeSpectrum.vanishingIdeal_mem_minimalPrimes]

/-- **The dimension of the special fibre of an affine chart.** Let `(A, 𝔪)` be a Noetherian
local domain of dimension at least one and let `W` be an affine scheme, locally of finite type
over `Spec A`, whose generic points are exactly the points lying over the generic point of
`Spec A`. Then the fibre of `W` over the closed point has dimension at most `dim(A) - 1` at
each of its points. -/
theorem topologicalKrullDimAt_fiber_add_one_le_ringKrullDim
    {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    {W : Scheme.{u}} [IsAffine W] (g : W ⟶ Spec (.of A)) [LocallyOfFiniteType g]
    (hdim : 1 ≤ ringKrullDim A)
    (hgen : ∀ v : W, v ∈ genericPoints W ↔ g v = genericPoint (Spec (.of A)))
    (u : W) (hu : g u = IsLocalRing.closedPoint A) :
    topologicalKrullDimAt (g.fiber (g u)) (g.asFiber u) + 1 ≤ ringKrullDim A := by
  have : IsDomain (CommRingCat.of A) := ‹IsDomain A›
  set C : CommRingCat.{u} := Γ(W, ⊤) with hC
  set e : W ≃ₜ Spec C := Scheme.homeoOfIso W.isoSpec with he
  set ψ : CommRingCat.of A ⟶ C := Spec.preimage (W.isoSpec.inv ≫ g) with hψ
  have hmap : Spec.map ψ = W.isoSpec.inv ≫ g := Spec.map_preimage _
  -- Present the chart as the spectrum of an `A`-algebra of finite type.
  let _ : Algebra A C := ψ.hom.toAlgebra
  have halg : CommRingCat.ofHom (algebraMap A C) = ψ := rfl
  have hft : Algebra.FiniteType A C := by
    have : LocallyOfFiniteType (Spec.map ψ) := hmap ▸ inferInstance
    exact HasRingHomProperty.Spec_iff.mp this
  -- Points of the chart are primes of that algebra, and the chart morphism is contraction.
  have hpt : ∀ q : PrimeSpectrum C, g (e.symm q) = PrimeSpectrum.comap (algebraMap A C) q := by
    intro q
    change g (W.isoSpec.inv q) = _
    rw [show g (W.isoSpec.inv q) = (W.isoSpec.inv ≫ g) q from rfl, ← hmap, ← halg]
    rfl
  -- The generic hypothesis becomes the condition of the algebra statement.
  have hgen' : ∀ r : Ideal C, r.IsPrime → (r ∈ minimalPrimes C ↔ Ideal.under A r = ⊥) := by
    intro r hr
    have h₁ : r ∈ minimalPrimes C ↔ e.symm ⟨r, hr⟩ ∈ genericPoints W := by
      rw [← mem_genericPoints_spec_iff C ⟨r, hr⟩]
      exact (e.symm.mem_genericPoints_iff ⟨r, hr⟩).symm
    rw [h₁, hgen, hpt ⟨r, hr⟩, genericPoint_eq_bot_of_affine (CommRingCat.of A)]
    exact ⟨fun h ↦ congrArg PrimeSpectrum.asIdeal h, fun h ↦ PrimeSpectrum.ext h⟩
  -- The prime of the chart point lies over the maximal ideal of `A`.
  have hover : Ideal.under A (e u : PrimeSpectrum C).asIdeal = IsLocalRing.maximalIdeal A := by
    have h := hpt (e u)
    rw [Homeomorph.symm_apply_apply, hu] at h
    exact congrArg PrimeSpectrum.asIdeal h.symm
  -- Transport the local dimension of the fibre to the chart and then to the algebra.
  have hsq := topologicalKrullDimAt_fiber_eq_of_etale_square (Spec.map ψ) W.isoSpec.inv
    (𝟙 (Spec (CommRingCat.of A))) g (by rw [hmap, Category.comp_id]) (e u)
  rw [show W.isoSpec.inv (e u) = u from e.symm_apply_apply u] at hsq
  rw [← hsq, ← halg, topologicalKrullDimAt_fiber_specMap_eq A C (e u)]
  have : (e u : PrimeSpectrum C).asIdeal.IsPrime := (e u : PrimeSpectrum C).isPrime
  exact Algebra.relativeDimensionAt_add_one_le_ringKrullDim hdim hgen' _ hover

namespace Space

attribute [local instance] pointTopology

variable (A : Type u) [CommRing A] [IsLocalRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A)))

/-- Pullbacks of presheaves on the big fppf site over `Spec A` (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullback_presheaf_SpecialFibreDimension
    {X Y Z : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- The closed point of `Spec A`, for `A` local, as a point of the base valued in the residue
field `κ`: the structure morphism of `Spec κ` read as a `κ`-valued point. -/
def residueFieldPoint :
    FieldValuedPoint B (Spec (.of A)) hA
      (yoneda.obj (baseTerminal B (Spec (.of A)) hA)) :=
  FieldValuedPoint.map B (Spec (.of A)) hA (yoneda.obj (residueSpecOver A B hA))
    (yoneda.map (residueSpecToBase A B hA)) (residueSpecPoint A B hA)

/-- The point of `Spec A` underlying `AlgebraicGeometry.Space.residueFieldPoint` is the closed
point. -/
theorem pointsToScheme_class_residueFieldPoint :
    pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
        ((residueFieldPoint A B hA).class B (Spec (.of A)) hA _) =
      IsLocalRing.closedPoint A :=
  schemePoint_residueSpecPoint A B hA

/-- **Stacks 0AYJ, case (4).** Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension at
least one and let `f : X → Spec A` be a morphism of algebraic spaces which is locally of finite
type, with `X` decent, such that the points of `|X|` lying over the generic point of `Spec A`
are exactly the generic points of the irreducible components of `|X|`. Then the special fibre
`X_κ` has dimension at most `dim(A) - 1`.

The bound is proved one point of `X_κ` at a time: base change identifies the dimension of
`X_κ` at a point with the relative dimension of `f` over the closed point there, an affine
étale chart turns that into the dimension of the fibre of an affine scheme of finite type over
`Spec A`, and the generic hypothesis transported to the chart is the hypothesis of the
commutative-algebra bound on the special fibre. -/
@[stacks 0AYJ "case (4), X decent"]
theorem dimension_fieldFibre_add_one_le_ringKrullDim [IsDomain A] [IsNoetherianRing A]
    (hdim : 1 ≤ ringKrullDim A)
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f)
    (hdec : IsDecentSpace B (Spec (.of A)) hA X)
    (hgen : ∀ x : points B (Spec (.of A)) hA X,
      x ∈ genericPoints (points B (Spec (.of A)) hA X) ↔
        pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
            (pointsMap B (Spec (.of A)) hA X f x) = genericPoint (Spec (.of A)))
    (hfib : IsAlgebraicSpace B (Spec (.of A)) hA
      (fieldFibre B (Spec (.of A)) hA f (residueFieldPoint A B hA))) :
    dimension B (Spec (.of A)) hA
        (fieldFibre B (Spec (.of A)) hA f (residueFieldPoint A B hA)) hfib + 1
      ≤ ringKrullDim A := by
  set pv := yonedaEquiv.symm (residueFieldPoint A B hA).value with hpv
  have hYalg : IsAlgebraicSpace B (Spec (.of A)) hA
      (yoneda.obj (baseTerminal B (Spec (.of A)) hA)) :=
    isAlgebraicSpace_yoneda B (Spec (.of A)) hA _
  have hZalg : IsAlgebraicSpace B (Spec (.of A)) hA
      (yoneda.obj ((residueFieldPoint A B hA).siteObject B (Spec (.of A)) hA _)) :=
    isAlgebraicSpace_yoneda B (Spec (.of A)) hA _
  refine iSup_add_one_le fun w ↦ ?_
  -- The dimension of the special fibre at `w` is a natural number.
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp
    (dimensionAtPoint_ne_bot B (Spec (.of A)) hA _ hfib w)
  rw [← hd]
  -- Read it as the relative dimension of `f` at the point of `X` below `w`.
  have hrel : HasRelativeDimensionAt d B (Spec (.of A)) hA (pullback.snd f pv) w :=
    (relativeDimensionAt_fieldTarget_iff_dimensionAtPoint B (Spec (.of A)) hA hfib
      (residueFieldPoint A B hA) (pullback.snd f pv) w d).mpr hd.symm
  set x := pointsMap B (Spec (.of A)) hA _ (pullback.fst f pv) w with hx
  have hrelf : HasRelativeDimensionAt d B (Spec (.of A)) hA f x :=
    (hasRelativeDimensionAt_iff_of_isPullback' B (Spec (.of A)) hA d
      (IsPullback.of_hasPullback f pv).flip hX hYalg hZalg hf w).mp hrel
  -- `x` lies over the closed point of `Spec A`.
  have hxbase : pointsMap B (Spec (.of A)) hA X f x =
      (residueFieldPoint A B hA).class B (Spec (.of A)) hA _ := by
    rw [hx, ← Function.comp_apply (f := pointsMap B (Spec (.of A)) hA X f), ← pointsMap_comp,
      pullback.condition, pointsMap_comp, Function.comp_apply]
    exact FieldValuedPoint.pointsMap_eq_class B (Spec (.of A)) hA _ _
  -- An affine étale chart of `X` at `x`, with a field-valued representative of the point.
  obtain ⟨W, b, hWaff, hb, w₀, hw₀⟩ :=
    exists_affine_etale_chart_at_point B (Spec (.of A)) hA X hX x
  obtain ⟨p₀, rfl⟩ := Quot.exists_rep w₀
  -- The chart square over the terminal object of the site.
  set h₀ : W ⟶ baseTerminal B (Spec (.of A)) hA :=
    (Over.mkIdTerminal : IsTerminal (baseTerminal B (Spec (.of A)) hA)).from W with hh₀
  have hid : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (Spec (.of A)) hA)).presheaf
        (𝟙 (yoneda.obj (baseTerminal B (Spec (.of A)) hA))) :=
    presheaf_etale_id B (Spec (.of A)) hA _
  have hcomm : yoneda.map h₀ ≫ 𝟙 (yoneda.obj (baseTerminal B (Spec (.of A)) hA)) = b ≫ f :=
    (baseTerminal_yonedaIsTerminal B (Spec (.of A)) hA).hom_ext _ _
  set gm := (BigFppfOver.toScheme B (Spec (.of A)) hA).map h₀ with hgm
  -- The chart morphism is locally of finite type, and its source is affine.
  have hgmft : LocallyOfFiniteType gm := hf W _ b _ h₀ hb hid hcomm
  have hWa : IsAffine ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj W) := hWaff
  -- The image in `Spec A` of a point of the chart, read through the chart square.
  have hchartbase : ∀ q : FieldValuedPoint B (Spec (.of A)) hA (yoneda.obj W),
      pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
          (pointsMap B (Spec (.of A)) hA X f (pointsMap B (Spec (.of A)) hA (yoneda.obj W) b
            (q.class B (Spec (.of A)) hA (yoneda.obj W)))) =
        gm (schemePoint B (Spec (.of A)) hA W q) := by
    intro q
    rw [← Function.comp_apply (f := pointsMap B (Spec (.of A)) hA X f), ← pointsMap_comp,
      ← hcomm, Category.comp_id]
    exact schemePoint_map_yoneda B (Spec (.of A)) hA h₀ q
  -- The generic hypothesis, transported to the chart.
  have hgenW : ∀ v : (BigFppfOver.toScheme B (Spec (.of A)) hA).obj W,
      v ∈ genericPoints ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj W) ↔
        gm v = genericPoint (Spec (.of A)) := by
    intro v
    obtain ⟨q, rfl⟩ := exists_fieldValuedPoint_schemePoint_eq B (Spec (.of A)) hA W v
    have hbE : IsEtale B (Spec (.of A)) hA b :=
      (isEtale_iff_presheaf_of_yoneda B (Spec (.of A)) hA b).mpr hb
    have hcp : ChartPoint B (Spec (.of A)) hA W b (schemePoint B (Spec (.of A)) hA W q)
        (pointsMap B (Spec (.of A)) hA (yoneda.obj W) b
          (q.class B (Spec (.of A)) hA (yoneda.obj W))) := ⟨q, rfl, rfl⟩
    rw [← hchartbase q, ← hgen, mem_genericPoints_iff_localRingDimension_eq_zero
      B (Spec (.of A)) hA hX hdec,
      localRingDimension_eq_zero_iff_all_etale_genericPoints B (Spec (.of A)) hA hX]
    refine ⟨fun hv U a u ha hu ↦ ?_, fun hall ↦ hall W b _ hbE hcp⟩
    exact (localRingDimension_eq_zero_iff_all_etale_genericPoints
      B (Spec (.of A)) hA hX _).mp
      ((localRingDimension_eq_zero_iff_exists_etale_genericPoint
        B (Spec (.of A)) hA hX _).mpr ⟨W, b, _, hbE, hcp, hv⟩) U a u ha hu
  -- The chart point lies over the closed point.
  have huclosed : gm (schemePoint B (Spec (.of A)) hA W p₀) = IsLocalRing.closedPoint A := by
    rw [← hchartbase p₀, hw₀, hxbase]
    exact pointsToScheme_class_residueFieldPoint A B hA
  -- The chart equation for the relative dimension, and the affine bound.
  have hchart := hasRelativeDimensionAt_iff_of_chart B (Spec (.of A)) hA d f _
    (EtaleChartAtPoint.ofFieldValuedPoint B (Spec (.of A)) hA f W
      (baseTerminal B (Spec (.of A)) hA) b _ h₀ hb hid hcomm p₀)
  rw [EtaleChartAtPoint.sourcePoint_ofFieldValuedPoint] at hchart
  rw [← hw₀] at hrelf
  rw [← hchart.mp hrelf]
  exact topologicalKrullDimAt_fiber_add_one_le_ringKrullDim gm hdim hgenW _ huclosed

/-- **Stacks 0AYJ, case (3).** Let `(A, 𝔪, κ)` be a Noetherian local domain of dimension at
least one and let `f : X → Spec A` be a morphism of algebraic spaces which is locally of finite
type, with `X` integral, such that exactly one point of `|X|` lies over the generic point of
`Spec A`. Then the special fibre `X_κ` has dimension at most `dim(A) - 1`.

This is case (4): an integral algebraic space is decent and its space of points is
irreducible, so its generic points are the points whose closure is everything, and there is
one of them because the points of codimension zero are dense. The image of such a point both
specialises to and generalises the generic point of `Spec A`, hence equals it, and uniqueness
identifies it with the point lying over the generic point. Quasi-separatedness, which the
source also assumes, is not needed for this reduction. -/
@[stacks 0AYJ "case (3), X integral"]
theorem dimension_fieldFibre_add_one_le_ringKrullDim_of_isIntegralSpace
    [IsDomain A] [IsNoetherianRing A] (hdim : 1 ≤ ringKrullDim A)
    {X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)
    (f : X ⟶ yoneda.obj (baseTerminal B (Spec (.of A)) hA))
    (hf : IsLocallyOfFiniteType B (Spec (.of A)) hA f)
    (hint : IsIntegralSpace B (Spec (.of A)) hA X)
    (hone : ∃! x : points B (Spec (.of A)) hA X,
      pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
        (pointsMap B (Spec (.of A)) hA X f x) = genericPoint (Spec (.of A)))
    (hfib : IsAlgebraicSpace B (Spec (.of A)) hA
      (fieldFibre B (Spec (.of A)) hA f (residueFieldPoint A B hA))) :
    dimension B (Spec (.of A)) hA
        (fieldFibre B (Spec (.of A)) hA f (residueFieldPoint A B hA)) hfib + 1
      ≤ ringKrullDim A := by
  have hirr : IrreducibleSpace (points B (Spec (.of A)) hA X) := hint.irreducibleSpace
  have hdec : IsDecentSpace B (Spec (.of A)) hA X := hint.isDecentSpace
  -- The point space being irreducible, its generic points are the dense ones.
  have hgp : ∀ x : points B (Spec (.of A)) hA X,
      x ∈ genericPoints (points B (Spec (.of A)) hA X) ↔
        closure {x} = (Set.univ : Set (points B (Spec (.of A)) hA X)) := by
    intro x
    rw [genericPoints, Set.mem_ofPred_eq, irreducibleComponents_eq_singleton]
    exact Set.mem_singleton_iff
  -- A dense point exists because the points of codimension zero are dense.
  obtain ⟨η, hη⟩ : ∃ η : points B (Spec (.of A)) hA X,
      closure {η} = (Set.univ : Set (points B (Spec (.of A)) hA X)) := by
    obtain ⟨η, hηmem⟩ := (codimensionZeroPoints_dense B (Spec (.of A)) hA hX).nonempty
    exact ⟨η, (hgp η).mp ((mem_genericPoints_iff_localRingDimension_eq_zero
      B (Spec (.of A)) hA hX hdec η).mpr hηmem)⟩
  have hcont : Continuous (fun x : points B (Spec (.of A)) hA X ↦
      pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
        (pointsMap B (Spec (.of A)) hA X f x)) :=
    (schemePointsHomeomorph B (Spec (.of A)) hA _).continuous.comp
      (continuous_pointsMap B (Spec (.of A)) hA f)
  -- A dense point is carried to the generic point of the base.
  have hkey : ∀ y : points B (Spec (.of A)) hA X,
      closure {y} = (Set.univ : Set (points B (Spec (.of A)) hA X)) →
        pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
          (pointsMap B (Spec (.of A)) hA X f y) = genericPoint (Spec (.of A)) := by
    intro y hy
    obtain ⟨x₀, hx₀, -⟩ := hone
    have hspec : y ⤳ x₀ := specializes_iff_mem_closure.mpr (hy ▸ Set.mem_univ x₀)
    have h₁ : pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
        (pointsMap B (Spec (.of A)) hA X f y) ⤳ genericPoint (Spec (.of A)) := by
      rw [← hx₀]
      exact hspec.map hcont
    have h₂ : genericPoint (Spec (.of A)) ⤳
        pointsToScheme B (Spec (.of A)) hA (baseTerminal B (Spec (.of A)) hA)
          (pointsMap B (Spec (.of A)) hA X f y) := genericPoint_specializes _
    exact (h₁.antisymm h₂).eq
  obtain ⟨x₀, hx₀, huniq⟩ := hone
  refine dimension_fieldFibre_add_one_le_ringKrullDim A B hA hdim hX f hf hdec
    (fun x ↦ ⟨fun hx ↦ hkey x ((hgp x).mp hx), fun hx ↦ ?_⟩) hfib
  rw [huniq x hx, ← huniq η (hkey η hη)]
  exact (hgp η).mpr hη

end Space

end AlgebraicGeometry

end
