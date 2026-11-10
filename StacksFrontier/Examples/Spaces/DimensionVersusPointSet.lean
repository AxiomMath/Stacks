module

public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.BirationalCurveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.ComplementaryCurve.Components
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Dimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelationSummands
public import StacksFrontier.AlgebraicGeometry.Spaces.PointTopologyEtaleOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.InfiniteProductQuotientPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Presentation.Points
public import StacksFrontier.AlgebraicGeometry.Spaces.PresentationFromQuotient
public import StacksFrontier.AlgebraicGeometry.Topologies.BigFppfOverTypeSheafification
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.Examples.Spaces.NonSeparatedGroupSpace
public import StacksFrontier.Topology.Dimension.IsolatedPoint
public import StacksFrontier.Topology.Dimension.KrullSeparation
public import StacksFrontier.Topology.Dimension.LocalKrullDim

/-!
# The dimension of an algebraic space is not the dimension of its point space

Over a field `k` of characteristic zero the quotient `𝔸¹_k/ℤ` of the affine line by the
integer translations has dimension `1` at each of its points, because the affine line is an
étale chart and has local dimension `1` everywhere, while its point space carries the
indiscrete topology and so has Krull dimension `0`. The two dimensions therefore differ at
every point, which is the first example of **Stacks 0DRF**.

The second example of that remark is the algebraic space `X = U/R` of Stacks 02Z8, built from
`U = Spec (∏ n : ℕ, K)` for a finite field `K`. It runs the other way: `U` is an étale chart
whose point space is `T₁` and sober, so `X` has dimension `0` at each of its points, while
`|X|` is irreducible of Krull dimension `1` with the image `x₀` of the section `S ⟶ X` as a
generic point. The local Krull dimension of `|X|` is `1` at every point other than `x₀`, and
there the two dimensions differ again; at `x₀` itself the remark's parenthetical claim is
inaccurate and both dimensions are `0`.

## Main results

All of them are in the namespace `Stacks.Examples.DimensionVersusPointSet`.

* `dimensionAtPoint_translationQuotient_eq_one`: the
  dimension of `𝔸¹_k/ℤ` at each of its points is `1`.
* `topologicalKrullDim_points_translationQuotient_eq_zero`:
  the point space of `𝔸¹_k/ℤ` is of Krull dimension `0`, being indiscrete.
* `dimensionAtPoint_ne_topologicalKrullDimAt_points`:
  at every point of `𝔸¹_k/ℤ` the dimension of the space differs from the local Krull
  dimension of its point space.
* `dimensionAtPoint_infiniteProductQuotient_eq_zero`:
  the space `X = U/R` of Stacks 02Z8 has dimension `0` at each of its points.
* `irreducibleSpace_points_infiniteProductQuotient`,
  `isGenericPoint_quotientCoordinatePoint` and
  `topologicalKrullDim_points_infiniteProductQuotient_eq_one`:
  `|X|` is irreducible, admits `x₀` as a generic point, and is of Krull dimension `1`.
* `topologicalKrullDimAt_points_infiniteProductQuotient_eq_one`
  and
  `dimensionAtPoint_ne_topologicalKrullDimAt_points_infiniteProductQuotient`:
  the local Krull dimension of `|X|` is `1` at every point other than `x₀`, so there the two
  dimensions differ in the direction opposite to the first example, while
  `topologicalKrullDimAt_quotientCoordinatePoint_eq_zero`
  records that at `x₀` it is `0`.
* `exists_dimensionAtPoint_eq_zero_topologicalKrullDim_points_eq_one`:
  the second example with no parameters left, over the field with two elements.

## Implementation notes

Indiscreteness of the point space comes from the chart: the map on points of a surjective
étale chart is a quotient map, so an open subset of `|𝔸¹_k/ℤ|` is cut out by a translation
invariant open subset of `𝔸¹_k`. Transporting such a subset to `Spec k[X]`, its complement
is a translation invariant closed subset, and if it is nonempty it contains a nonzero prime
`(p)`; a nonzero element `f` of the vanishing ideal is then divisible by every integer
translate of `p`, so a root of `p` in an algebraic closure produces infinitely many roots of
`f`. In characteristic zero that is impossible, so the complement is empty.

The dimension at a point is computed on the chart by
`AlgebraicGeometry.Space.dimensionAtPoint_eq_of_etale_chart`, the local dimension of the
affine line being `1` at every point because the line is irreducible of dimension `1` and of
finite type over the field.

For the second example the chart is `U = Spec (∏ n : ℕ, K)`, whose points are all closed by
`AlgebraicGeometry.Space.InfiniteProduct.isClosed_singleton`, so the chart has Krull dimension
`0` and `X` has dimension `0` at each point. The Krull dimension of `|X|` is computed from the
two shapes an irreducible closed subset of `|X|` can have: one containing `x₀` is everything,
the closure of `x₀` being everything, and one avoiding `x₀` is minimal, because over such a
subset the fibres of the open surjection `|U| → |X|` are single points — only the coordinate
points of `U` are identified in `X` — so its preimage is irreducible, and `|U|` carries no
strict chain of irreducible closed subsets.

## References

* [Stacks Project, Tag 02Z7](https://stacks.math.columbia.edu/tag/02Z7)
* [Stacks Project, Tag 04N5](https://stacks.math.columbia.edu/tag/04N5)
* [Stacks Project, Tag 02Z8](https://stacks.math.columbia.edu/tag/02Z8)
* [Stacks Project, Tag 0DRF](https://stacks.math.columbia.edu/tag/0DRF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Examples.DimensionVersusPointSet

/-! ### Integer translates of a polynomial -/

/-- In characteristic zero no nonzero polynomial is divisible by all the integer translates
of a nonconstant polynomial: a root of the latter in an algebraic closure produces an
infinite family of roots of the former. -/
theorem not_forall_dvd_comp_X_add_intCast {k : Type u} [Field k] [CharZero k]
    {f p : Polynomial k} (hf : f ≠ 0) (hp : 0 < p.natDegree)
    (h : ∀ n : ℤ, p ∣ f.comp (Polynomial.X + (n : Polynomial k))) : False := by
  classical
  have hinj : Function.Injective (algebraMap k (AlgebraicClosure k)) :=
    (algebraMap k (AlgebraicClosure k)).injective
  have : CharZero (AlgebraicClosure k) := charZero_of_injective_algebraMap hinj
  set φ : k →+* AlgebraicClosure k := algebraMap k (AlgebraicClosure k) with hφ
  have hpdeg : (p.map φ).degree ≠ 0 := by
    rw [Polynomial.degree_map]
    intro hd
    have h0 : p.natDegree = 0 :=
      Polynomial.natDegree_eq_zero_iff_degree_le_zero.mpr hd.le
    omega
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_root (p.map φ) hpdeg
  have hfmap : f.map φ ≠ 0 := (Polynomial.map_ne_zero_iff hinj).mpr hf
  have key : ∀ n : ℤ, (f.map φ).IsRoot (y + (n : AlgebraicClosure k)) := by
    intro n
    obtain ⟨c, hc⟩ := h n
    have hmap := congrArg (Polynomial.map φ) hc
    rw [Polynomial.map_comp, Polynomial.map_mul] at hmap
    have hev := congrArg (fun q : Polynomial (AlgebraicClosure k) => q.eval y) hmap
    simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.map_add, Polynomial.map_X, Polynomial.map_intCast, Polynomial.eval_intCast,
      Polynomial.eval_mul] at hev
    rw [Polynomial.IsRoot.def]
    rw [hev, Polynomial.IsRoot.def.mp hy, zero_mul]
  exact Set.infinite_range_of_injective
    (f := fun n : ℤ => y + (n : AlgebraicClosure k))
    (fun a b hab => Int.cast_injective (add_left_cancel hab))
    (Set.Finite.subset (Polynomial.finite_setOfPred_isRoot hfmap)
      (Set.range_subset_iff.mpr key))

/-! ### Translation invariant open subsets of the affine line -/

/-- Translation of the variable by an integer, as an endomorphism of the polynomial ring. -/
def shiftHom (k : Type u) [Field k] (n : ℤ) : Polynomial k →+* Polynomial k :=
  Polynomial.eval₂RingHom (Polynomial.C : k →+* Polynomial k)
    (Polynomial.X + (n : Polynomial k))

theorem shiftHom_apply {k : Type u} [Field k] (n : ℤ) (f : Polynomial k) :
    shiftHom k n f = f.comp (Polynomial.X + (n : Polynomial k)) := rfl

@[simp]
theorem shiftHom_X {k : Type u} [Field k] (n : ℤ) :
    shiftHom k n Polynomial.X = Polynomial.X + (n : Polynomial k) :=
  Polynomial.eval₂_X _ _

@[simp]
theorem shiftHom_C {k : Type u} [Field k] (n : ℤ) (a : k) :
    shiftHom k n (Polynomial.C a) = Polynomial.C a :=
  Polynomial.eval₂_C _ _

/-- A nonempty open subset of `Spec k[X]` invariant under all the integer translations of the
variable is the whole space, when `k` has characteristic zero. Its complement is closed and
invariant; a nonzero element of an ideal cutting it out is divisible by every translate of a
generator of a point of the complement. -/
theorem eq_univ_of_isOpen_of_shiftHom_invariant {k : Type u} [Field k] [CharZero k]
    (W : Set (PrimeSpectrum (Polynomial k))) (hWopen : IsOpen W) (hWne : W.Nonempty)
    (hinv : ∀ (n : ℤ) (w : PrimeSpectrum (Polynomial k)),
      PrimeSpectrum.comap (shiftHom k n) w ∈ W ↔ w ∈ W) :
    W = Set.univ := by
  classical
  by_contra hne
  obtain ⟨z, hz⟩ : (Wᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact hne
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus (Wᶜ)).mp hWopen.isClosed_compl
  -- A nonzero element of `I`, obtained from the generic point.
  obtain ⟨f, hfI, hf0⟩ : ∃ f ∈ I, f ≠ 0 := by
    by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    refine absurd ?_ hWne.ne_empty
    have huniv : Wᶜ = Set.univ := by
      rw [hI]
      refine Set.eq_univ_of_forall fun q => ?_
      rw [PrimeSpectrum.mem_zeroLocus]
      intro g hg
      rw [hall g hg]
      exact zero_mem _
    rw [← Set.compl_univ_iff, huniv]
  -- The point `z` of the complement is a nonzero prime, hence generated by an irreducible.
  have hfz : f ∈ z.asIdeal := by
    rw [hI] at hz
    exact hz hfI
  set p : Polynomial k := Submodule.IsPrincipal.generator z.asIdeal with hpdef
  have hspan : Ideal.span {p} = z.asIdeal := Ideal.span_singleton_generator z.asIdeal
  have hzbot : z.asIdeal ≠ ⊥ := fun h0 => hf0 (by
    rw [h0] at hfz
    simpa using hfz)
  have hp0 : p ≠ 0 := by
    intro h0
    refine hzbot ?_
    rw [← hspan, h0]
    simp
  have hpprime : Prime p :=
    (Ideal.span_singleton_prime hp0).mp (by rw [hspan]; exact z.isPrime)
  have hpdeg : 0 < p.natDegree := by
    rcases Nat.eq_zero_or_pos p.natDegree with hd | hd
    · obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp hd
      have ha0 : a ≠ 0 := fun h0 => hp0 (by rw [← ha, h0, map_zero])
      exact absurd (show IsUnit p by
        rw [← ha]
        exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr ha0)) hpprime.not_isUnit
    · exact hd
  -- Every integer translate of `p` divides `f`.
  refine not_forall_dvd_comp_X_add_intCast hf0 hpdeg ?_
  intro n
  have hmem : f ∈ (PrimeSpectrum.comap (shiftHom k n) z).asIdeal := by
    have hzn : PrimeSpectrum.comap (shiftHom k n) z ∈ Wᶜ := fun hc =>
      hz ((hinv n z).mp hc)
    rw [hI] at hzn
    exact hzn hfI
  rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, ← hspan,
    Ideal.mem_span_singleton] at hmem
  exact hmem

/-! ### The affine line as the spectrum of a polynomial ring -/

open AffineLineInvolution AffineLineTranslation

variable (k : Type u) [Field k]

/-- The affine line over `k` as the spectrum of the polynomial ring in one variable. -/
def lineSpecIso : (affineLine k).left ≅ Spec (.of (Polynomial k)) :=
  (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).trans
    (Scheme.Spec.mapIso
      ((MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).toRingEquiv.toCommRingCatIso.op)).symm

theorem lineSpecIso_inv_eq :
    (lineSpecIso k).inv =
      Spec.map (CommRingCat.ofHom
          (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).toRingEquiv.toRingHom) ≫
        (AffineSpace.SpecIso PUnit.{u + 1} (.of k)).inv :=
  rfl

theorem lineSpecIso_inv_appTop_coord :
    (lineSpecIso k).inv.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit) =
      (Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X := by
  rw [lineSpecIso_inv_eq, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    AffineSpace.SpecIso_inv_appTop_coord, Scheme.specMap_appTop_ΓSpecIso_inv]
  congr 1
  simp

/-- The identification of `k[X]` with the polynomial ring in the single variable of affine
space carries the inclusion of the constants to the inclusion of the constants. -/
theorem uniqueAlgEquiv_comp_C :
    (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}).toRingEquiv.toRingHom.comp
        (MvPolynomial.C : k →+* MvPolynomial PUnit.{u + 1} k) =
      (Polynomial.C : k →+* Polynomial k) := by
  refine RingHom.ext fun a => ?_
  change (MvPolynomial.uniqueAlgEquiv k PUnit.{u + 1}) (MvPolynomial.C a) = Polynomial.C a
  rw [show (MvPolynomial.C a : MvPolynomial PUnit.{u + 1} k) =
    algebraMap k (MvPolynomial PUnit.{u + 1} k) a from rfl,
    AlgEquiv.commutes]
  rfl

theorem lineSpecIso_inv_over :
    (lineSpecIso k).inv ≫ ((AffineSpace PUnit.{u + 1} (Spec (.of k))) ↘ Spec (.of k)) =
      Spec.map (CommRingCat.ofHom (Polynomial.C : k →+* Polynomial k)) := by
  rw [lineSpecIso_inv_eq, Category.assoc, AffineSpace.SpecIso_inv_over, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, uniqueAlgEquiv_comp_C]

theorem translationAction_left_eq (n : ℤ) :
    ((translationAction k (Multiplicative.ofAdd n)).asIso.hom.left) =
      (lineSpecIso k).hom ≫ Spec.map (CommRingCat.ofHom (shiftHom k n)) ≫
        (lineSpecIso k).inv := by
  apply AffineSpace.hom_ext
  · rw [Category.assoc, Category.assoc, lineSpecIso_inv_over, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp,
      show (shiftHom k n).comp (Polynomial.C : k →+* Polynomial k) =
          (Polynomial.C : k →+* Polynomial k) from RingHom.ext fun a => shiftHom_C n a,
      ← lineSpecIso_inv_over, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
    exact Over.w ((translationAction k (Multiplicative.ofAdd n)).asIso.hom)
  · intro i
    obtain rfl : i = PUnit.unit := Subsingleton.elim _ _
    rw [translationAction_apply]
    rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply, lineSpecIso_inv_appTop_coord,
      Scheme.specMap_appTop_ΓSpecIso_inv, CommRingCat.hom_ofHom, shiftHom_X]
    have hcoord : (lineSpecIso k).hom.appTop
        ((Scheme.ΓSpecIso (.of (Polynomial k))).inv Polynomial.X) =
        AffineSpace.coord (Spec (.of k)) PUnit.unit := by
      have h := congrArg
        (fun m : (affineLine k).left ⟶ (affineLine k).left =>
          m.appTop (AffineSpace.coord (Spec (.of k)) PUnit.unit))
        (lineSpecIso k).hom_inv_id
      simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
        lineSpecIso_inv_appTop_coord] at h
      simpa using h
    simp only [map_add, map_intCast]
    rw [hcoord]

/-- A nonempty open subset of the affine line over a field of characteristic zero invariant
under the integer translations is the whole line. -/
theorem eq_univ_of_isOpen_of_translation_invariant [CharZero k]
    (V : Set ((affineLine k).left)) (hVopen : IsOpen V) (hVne : V.Nonempty)
    (hinv : ∀ (n : ℤ) (y : (affineLine k).left),
      ((translationAction k (Multiplicative.ofAdd n)).asIso.hom.left) y ∈ V ↔ y ∈ V) :
    V = Set.univ := by
  have hinvhom : ∀ y : (affineLine k).left,
      (lineSpecIso k).inv ((lineSpecIso k).hom y) = y := by
    intro y
    rw [← Scheme.Hom.comp_apply, Iso.hom_inv_id]
    simp
  have hhominv : ∀ w : Spec (.of (Polynomial k)),
      (lineSpecIso k).hom ((lineSpecIso k).inv w) = w := by
    intro w
    rw [← Scheme.Hom.comp_apply, Iso.inv_hom_id]
    simp
  have hbase : ∀ (n : ℤ) (w : Spec (.of (Polynomial k))),
      ((translationAction k (Multiplicative.ofAdd n)).asIso.hom.left) ((lineSpecIso k).inv w) =
        (lineSpecIso k).inv (PrimeSpectrum.comap (shiftHom k n) w) := by
    intro n w
    rw [translationAction_left_eq k n, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hhominv]
    rfl
  have hWuniv : ((lineSpecIso k).inv ⁻¹' V) = Set.univ := by
    refine eq_univ_of_isOpen_of_shiftHom_invariant ((lineSpecIso k).inv ⁻¹' V)
      (hVopen.preimage (lineSpecIso k).inv.continuous) ?_ ?_
    · obtain ⟨y, hy⟩ := hVne
      refine ⟨(lineSpecIso k).hom y, ?_⟩
      change (lineSpecIso k).inv ((lineSpecIso k).hom y) ∈ V
      rw [hinvhom]
      exact hy
    · intro n w
      change (lineSpecIso k).inv (PrimeSpectrum.comap (shiftHom k n) w) ∈ V ↔
        (lineSpecIso k).inv w ∈ V
      rw [← hbase n w]
      exact hinv n _
  refine Set.eq_univ_of_forall fun y => ?_
  have hy : (lineSpecIso k).hom y ∈ ((lineSpecIso k).inv ⁻¹' V) := by
    rw [hWuniv]; trivial
  have hy' : (lineSpecIso k).inv ((lineSpecIso k).hom y) ∈ V := hy
  rw [hinvhom] at hy'
  exact hy'

/-! ### The dimension of the affine line at a point -/

/-- The affine line over a field has local dimension one at every point: it is irreducible of
dimension one and of finite type over the field. -/
theorem topologicalKrullDimAt_affineLine (y : (affineLine k).left) :
    topologicalKrullDimAt ((affineLine k).left) y = 1 := by
  have : LocallyOfFiniteType ((affineLine k).hom) :=
    (inferInstance : LocallyOfFiniteType
      ((AffineSpace PUnit.{u + 1} (Spec (.of k))) ↘ Spec (.of k)))
  have : PreirreducibleSpace ((affineLine k).left) :=
    (inferInstance : PreirreducibleSpace (AffineSpace PUnit.{u + 1} (Spec (.of k))))
  exact Stacks.Curves.topologicalKrullDimAt_eq_one_of_equidimensional _ ((affineLine k).hom)
    (TopologicalSpace.Equidimensional.of_preirreducibleSpace _)
    (topologicalKrullDim_affineSpace k PUnit.{u + 1}) y

/-! ### The quotient of the affine line by the integer translations -/

open NonSeparatedGroupSpace

attribute [local instance] AlgebraicGeometry.Space.pointTopology

variable [CharZero k] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of k)))
  [HasSheafify (BigFppfOver.topology B (Spec (.of k)) hS) (Type u)]

/-- **Stacks 0DRF.** The dimension of `𝔸¹_k/ℤ` at each of its points is `1`: the affine line
is a surjective étale chart and has local dimension `1` at every point. -/
@[stacks 0DRF "the first counterexample: 𝔸¹_k/ℤ has dimension 1 at every point"]
theorem dimensionAtPoint_translationQuotient_eq_one
    (x : Space.points B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS))) :
    Space.dimensionAtPoint B (Spec (.of k)) hS
        (translationQuotient k B hS (contains_affineLine k B hS))
        (isAlgebraicSpace_translationQuotient k B hS) x = 1 := by
  obtain ⟨q, hq⟩ := (Space.surjective_iff_surjective_pointsMap B (Spec (.of k)) hS _
    (isAlgebraicSpace_translationQuotient k B hS) (lineObj k B hS)
    (lineChart k B hS)).mp (surjective_lineChart k B hS) x
  obtain ⟨p, hp⟩ := Quot.exists_rep q
  rw [← hp] at hq
  rw [Space.dimensionAtPoint_eq_of_etale_chart B (Spec (.of k)) hS _
    (isAlgebraicSpace_translationQuotient k B hS) x (lineObj k B hS) (lineChart k B hS)
    (etale_lineChart k B hS) p hq]
  exact topologicalKrullDimAt_affineLine k _

/-- The map from the points of the affine line to the points of `𝔸¹_k/ℤ`, read through the
identification of the points of a represented presheaf with the points of the representing
scheme. -/
def chartPointsMap : (affineLine k).left →
    Space.points B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS)) :=
  fun y => Space.pointsMap B (Spec (.of k)) hS _ (lineChart k B hS)
    ((Space.schemePointsHomeomorph B (Spec (.of k)) hS (lineObj k B hS)).symm y)

theorem continuous_chartPointsMap : Continuous (chartPointsMap k B hS) :=
  (Space.continuous_pointsMap B (Spec (.of k)) hS (lineChart k B hS)).comp
    (Space.schemePointsHomeomorph B (Spec (.of k)) hS (lineObj k B hS)).symm.continuous

theorem surjective_chartPointsMap : Function.Surjective (chartPointsMap k B hS) :=
  Function.Surjective.comp
    ((Space.surjective_iff_surjective_pointsMap B (Spec (.of k)) hS _
      (isAlgebraicSpace_translationQuotient k B hS) (lineObj k B hS)
      (lineChart k B hS)).mp (surjective_lineChart k B hS))
    (Space.schemePointsHomeomorph B (Spec (.of k)) hS (lineObj k B hS)).symm.surjective

/-- Two points of the affine line differing by an integer translation have the same image in
`𝔸¹_k/ℤ`: the summand of the relation scheme indexed by that integer carries one to the
other. -/
theorem chartPointsMap_translate (g : Multiplicative ℤ) (y : (affineLine k).left) :
    chartPointsMap k B hS ((translationAction k g).asIso.hom.left y) = chartPointsMap k B hS y := by
  unfold chartPointsMap
  have : Stacks.Groupoids.IsEtaleEquivalenceRelation
      (Space.relation B (Spec (.of k)) hS (lineRelationSource k B hS)
        (lineRelationTarget k B hS)) :=
    isEtaleEquivalenceRelation_translationActionRelation k
  have hz : ∀ w : (affineLine k).left,
      Space.pointsToScheme B (Spec (.of k)) hS (lineObj k B hS)
        ((Space.schemePointsHomeomorph B (Spec (.of k)) hS (lineObj k B hS)).symm w) = w :=
    fun w =>
      (Space.schemePointsHomeomorph B (Spec (.of k)) hS (lineObj k B hS)).apply_symm_apply w
  refine (Space.Presentation.pointsRelation_iff
    (Space.quotientPresentation B (Spec (.of k)) hS (lineRelationSource k B hS)
      (lineRelationTarget k B hS) (isAlgebraicSpace_translationQuotient k B hS)) _ _).mp ?_
  refine ⟨Space.pointsMap B (Spec (.of k)) hS _
    (yoneda.map (Space.siteActionRelationInclusion (Multiplicative ℤ) B hS (lineObj k B hS)
      (contains_lineRelationScheme k B hS) g))
    ((Space.schemePointsHomeomorph B (Spec (.of k)) hS (lineObj k B hS)).symm y), ?_, ?_⟩
  · change Space.pointsMap B (Spec (.of k)) hS _ (yoneda.map (lineRelationTarget k B hS))
        (Space.pointsMap B (Spec (.of k)) hS _
          (yoneda.map (Space.siteActionRelationInclusion (Multiplicative ℤ) B hS
            (lineObj k B hS) (contains_lineRelationScheme k B hS) g))
          ((Space.schemePointsHomeomorph B (Spec (.of k)) hS (lineObj k B hS)).symm y)) =
      (Space.schemePointsHomeomorph B (Spec (.of k)) hS (lineObj k B hS)).symm
        ((translationAction k g).asIso.hom.left y)
    refine Space.injective_pointsToScheme B (Spec (.of k)) hS (lineObj k B hS) ?_
    have hmap : (BigFppfOver.toScheme B (Spec (.of k)) hS).map
        (Space.siteActionRelationInclusion (Multiplicative ℤ) B hS (lineObj k B hS)
            (contains_lineRelationScheme k B hS) g ≫ lineRelationTarget k B hS) =
        ((translationAction k g).asIso.hom.left) :=
      Space.toScheme_map_siteActionRelationInclusion_comp_target (Multiplicative ℤ) B hS
        (lineObj k B hS) (contains_lineRelationScheme k B hS) (translationAction k) g
    rw [← Space.pointsMap_comp_apply, ← Functor.map_comp,
      Space.pointsToScheme_pointsMap, hz, hz]
    exact congrArg (fun m : (affineLine k).left ⟶ (affineLine k).left => m y) hmap
  · change Space.pointsMap B (Spec (.of k)) hS _ (yoneda.map (lineRelationSource k B hS))
        (Space.pointsMap B (Spec (.of k)) hS _
          (yoneda.map (Space.siteActionRelationInclusion (Multiplicative ℤ) B hS
            (lineObj k B hS) (contains_lineRelationScheme k B hS) g))
          ((Space.schemePointsHomeomorph B (Spec (.of k)) hS (lineObj k B hS)).symm y)) =
      (Space.schemePointsHomeomorph B (Spec (.of k)) hS (lineObj k B hS)).symm y
    rw [← Space.pointsMap_comp_apply, ← Functor.map_comp,
      Space.siteActionRelationInclusion_comp_source, CategoryTheory.Functor.map_id,
      Space.pointsMap_id, id_eq]

/-- The point space of `𝔸¹_k/ℤ` is indiscrete: an open subset pulls back along the chart to a
translation invariant open subset of the affine line, which is empty or everything. -/
theorem indiscreteTopology_points_translationQuotient :
    IndiscreteTopology (Space.points B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS))) := by
  have hsurj : Function.Surjective (chartPointsMap k B hS) :=
    surjective_chartPointsMap k B hS
  have hdich : ∀ W : Set (Space.points B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS))), IsOpen W →
      W = ∅ ∨ W = Set.univ := by
    intro W hW
    have hVopen : IsOpen (chartPointsMap k B hS ⁻¹' W) :=
      hW.preimage (continuous_chartPointsMap k B hS)
    rcases Set.eq_empty_or_nonempty (chartPointsMap k B hS ⁻¹' W) with hVe | hVne
    · exact Or.inl (hsurj.preimage_injective (by rw [hVe, Set.preimage_empty]))
    · refine Or.inr (hsurj.preimage_injective ?_)
      have hVuniv := eq_univ_of_isOpen_of_translation_invariant k _ hVopen hVne (by
        intro n y
        rw [Set.mem_preimage, Set.mem_preimage,
          chartPointsMap_translate k B hS (Multiplicative.ofAdd n) y])
      rw [hVuniv, Set.preimage_univ]
  refine (indiscreteTopology_iff _).mpr (TopologicalSpace.ext_iff.mpr fun W => ?_)
  rw [TopologicalSpace.isOpen_top_iff]
  refine ⟨hdich W, ?_⟩
  rintro (rfl | rfl)
  · exact isOpen_empty
  · exact isOpen_univ

/-- **Stacks 0DRF.** The point space of `𝔸¹_k/ℤ` is of Krull dimension `0`, being
indiscrete. -/
@[stacks 0DRF "the first counterexample: the point space of 𝔸¹_k/ℤ is of Krull dimension 0"]
theorem topologicalKrullDim_points_translationQuotient_eq_zero :
    topologicalKrullDim (Space.points B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS))) = (0 : WithBot ℕ∞) := by
  have := indiscreteTopology_points_translationQuotient k B hS
  have : Nonempty (Space.points B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS))) := by
    obtain ⟨y⟩ := (inferInstance : Nonempty (AffineSpace PUnit.{u + 1} (Spec (.of k))))
    exact ⟨chartPointsMap k B hS y⟩
  exact topologicalKrullDim_eq_zero_of_indiscreteTopology

/-- The local Krull dimension of the point space of `𝔸¹_k/ℤ` is at most `0` at every
point. -/
theorem topologicalKrullDimAt_points_translationQuotient_le_zero
    (x : Space.points B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS))) :
    topologicalKrullDimAt (Space.points B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS))) x ≤ (0 : WithBot ℕ∞) :=
  (topologicalKrullDimAt_le_topologicalKrullDim x).trans
    (le_of_eq (topologicalKrullDim_points_translationQuotient_eq_zero k B hS))

/-- **Stacks 0DRF.** The dimension of an algebraic space at a point need not coincide with the
dimension of its point space at that point: for `𝔸¹_k/ℤ` over a field of characteristic zero
the former is `1` while the latter is `0`. -/
@[stacks 0DRF "the dimension at a point differs from the local dimension of the point space"]
theorem dimensionAtPoint_ne_topologicalKrullDimAt_points
    (x : Space.points B (Spec (.of k)) hS
      (translationQuotient k B hS (contains_affineLine k B hS))) :
    Space.dimensionAtPoint B (Spec (.of k)) hS
        (translationQuotient k B hS (contains_affineLine k B hS))
        (isAlgebraicSpace_translationQuotient k B hS) x ≠
      topologicalKrullDimAt (Space.points B (Spec (.of k)) hS
        (translationQuotient k B hS (contains_affineLine k B hS))) x := by
  intro hx
  have hle := topologicalKrullDimAt_points_translationQuotient_le_zero k B hS x
  rw [← hx, dimensionAtPoint_translationQuotient_eq_one k B hS x] at hle
  exact absurd hle (by simp)

/-! ### The second example: the quotient of the spectrum of an infinite product -/

section SecondExample

open AlgebraicGeometry.Space.InfiniteProduct

variable (K : Type u) [Field K] [Finite K] (B : BigFppfSite.{u})
  (hS : B.Contains (base K)) (hU : B.Contains (space K)) (hR : B.Contains (relation K))

/-- The point space of `U = Spec (∏ n : ℕ, K)` is `T₁` for a finite field `K`: every one of its
points is closed, which is Stacks 02Z8. -/
theorem t1Space_space : T1Space (space K) :=
  ⟨fun x ↦ Space.InfiniteProduct.isClosed_singleton K x⟩

/-- The point space of `U = Spec (∏ n : ℕ, K)` is of Krull dimension at most `0` for a finite
field `K`: it is `T₁`, every point being closed, and sober, being the space of a scheme, so its
irreducible closed subsets are precisely its points. -/
theorem topologicalKrullDim_space_le_zero : topologicalKrullDim (space K) ≤ 0 :=
  have := t1Space_space K
  _root_.Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space

/-- The local Krull dimension of `U = Spec (∏ n : ℕ, K)` is `0` at each of its points. -/
theorem topologicalKrullDimAt_space_eq_zero (u : space K) :
    topologicalKrullDimAt (space K) u = 0 :=
  le_antisymm ((topologicalKrullDimAt_le_topologicalKrullDim u).trans
    (topologicalKrullDim_space_le_zero K)) (topologicalKrullDimAt_nonneg u)

/-- The point space of the chart `U` of the example is `T₁`, being homeomorphic to the point
space of the scheme `U`. -/
theorem t1Space_points_spaceChart :
    T1Space (Space.points B (base K) hS (yoneda.obj (spaceChart K B hS hU))) :=
  have : T1Space ((BigFppfOver.toScheme B (base K) hS).obj (spaceChart K B hS hU)) :=
    ⟨fun x ↦ Space.InfiniteProduct.isClosed_singleton K x⟩
  (Space.schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm.t1Space

/-- The point space of the chart `U` of the example is of Krull dimension at most `0`. -/
theorem topologicalKrullDim_points_spaceChart_le_zero :
    topologicalKrullDim (Space.points B (base K) hS (yoneda.obj (spaceChart K B hS hU))) ≤ 0 :=
  have := t1Space_points_spaceChart K B hS hU
  have := (Space.schemePointsHomeomorph B (base K) hS
    (spaceChart K B hS hU)).isOpenEmbedding.quasiSober
  _root_.Stacks.Topology.Dimension.topologicalKrullDim_le_zero_of_quasiSober_of_t1Space

/-- The point of the point space of the chart `U` determined by the `n`-th coordinate morphism
`S ⟶ U`. -/
noncomputable def coordinateChartPoint (n : ℕ) :
    Space.points B (base K) hS (yoneda.obj (spaceChart K B hS hU)) :=
  (Space.schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm
    ((coordinate K n).base (default : base K))

omit [Finite K] in
/-- The underlying morphism of schemes of the charted target projection is the target
projection of `R`. -/
theorem toScheme_map_chartTarget :
    (BigFppfOver.toScheme B (base K) hS).map (chartTarget K B hS hU hR) = relationTarget K :=
  congrArg Over.Hom.left (post_chartTarget K B hS hU hR)

omit [Finite K] in
/-- The underlying morphism of schemes of the charted source projection is the source
projection of `R`. -/
theorem toScheme_map_chartSource :
    (BigFppfOver.toScheme B (base K) hS).map (chartSource K B hS hU hR) = relationSource K :=
  congrArg Over.Hom.left (post_chartSource K B hS hU hR)

section Quotient

variable [HasSheafify (BigFppfOver.topology B (base K) hS) (Type u)]

/-- **Stacks 0DRF.** The algebraic space `X = U/R` of Stacks 02Z8 has dimension `0` at each of
its points: `U = Spec (∏ n : ℕ, K)` is an étale chart surjective on points, and its point space
is `T₁` and sober, hence of local Krull dimension `0` at every one of its points. -/
@[stacks 0DRF "the second counterexample: the space X = U/R of Stacks 02Z8 has dimension 0 at \
  every point"]
theorem dimensionAtPoint_infiniteProductQuotient_eq_zero
    (x : Space.points B (base K) hS (quotient K B hS hU hR)) :
    Space.dimensionAtPoint B (base K) hS (quotient K B hS hU hR)
        (isAlgebraicSpace_quotient K B hS hU hR) x = 0 := by
  obtain ⟨q, hq⟩ := Space.Presentation.pointsMap_surjective (presentation K B hS hU hR) x
  obtain ⟨p, hp⟩ := Quot.exists_rep q
  rw [← hp] at hq
  rw [Space.dimensionAtPoint_eq_of_etale_chart B (base K) hS _
    (isAlgebraicSpace_quotient K B hS hU hR) x (spaceChart K B hS hU)
    (Space.quotientMap B (base K) hS (chartSource K B hS hU hR) (chartTarget K B hS hU hR))
    (quotientMap_etale K B hS hU hR) p hq]
  exact topologicalKrullDimAt_space_eq_zero K _

/-- The point `x₀` of the point space of `X = U/R`: the image of the section `S ⟶ X` of
Stacks 02Z8, equivalently the common image of all the coordinate points of `U`. -/
noncomputable def quotientCoordinatePoint :
    Space.points B (base K) hS (quotient K B hS hU hR) :=
  Space.pointsMap B (base K) hS (yoneda.obj (baseChart K B hS))
    (coordinatePoint K B hS hU hR) (basePoint K B hS)

omit [Finite K] in
/-- Every coordinate point of the point space of the chart `U` maps to `x₀`. -/
theorem pointsMap_quotientMap_coordinateChartPoint (n : ℕ) :
    Space.pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
        (Space.quotientMap B (base K) hS (chartSource K B hS hU hR)
          (chartTarget K B hS hU hR)) (coordinateChartPoint K B hS hU n) =
      quotientCoordinatePoint K B hS hU hR :=
  pointsMap_quotientMap_coordinatePoint K B hS hU hR n

omit [Finite K] [HasSheafify (BigFppfOver.topology B (base K) hS) (Type u)] in
/-- The point space of the base `S` of the example has one point, `S` being the spectrum of a
field. -/
theorem subsingleton_points_baseChart :
    Subsingleton (Space.points B (base K) hS (yoneda.obj (baseChart K B hS))) :=
  have : Subsingleton ((BigFppfOver.toScheme B (base K) hS).obj (baseChart K B hS)) :=
    inferInstanceAs (Subsingleton (base K : Type u))
  (Space.schemePointsHomeomorph B (base K) hS (baseChart K B hS)).injective.subsingleton

omit [Finite K] in
/-- **Stacks 0DRF.** The point `x₀` is a generic point of the point space of `X = U/R`: the
coordinate points are dense in `|U|` and all of them map to `x₀`, which is Stacks 02Z8. -/
@[stacks 0DRF "the second counterexample: |X| admits x₀ as a generic point"]
theorem isGenericPoint_quotientCoordinatePoint :
    IsGenericPoint (quotientCoordinatePoint K B hS hU hR)
      (Set.univ : Set (Space.points B (base K) hS (quotient K B hS hU hR))) := by
  have hsub := subsingleton_points_baseChart K B hS
  have hrange : Set.range (Space.pointsMap B (base K) hS (yoneda.obj (baseChart K B hS))
      (coordinatePoint K B hS hU hR)) ⊆ {quotientCoordinatePoint K B hS hU hR} := by
    rintro _ ⟨p, rfl⟩
    rw [Set.mem_singleton_iff, quotientCoordinatePoint,
      Subsingleton.elim p (basePoint K B hS)]
  have hdense : Dense ({quotientCoordinatePoint K B hS hU hR} :
      Set (Space.points B (base K) hS (quotient K B hS hU hR))) :=
    (dense_range_pointsMap_coordinatePoint K B hS hU hR).mono hrange
  exact dense_iff_closure_eq.mp hdense

omit [Finite K] in
/-- **Stacks 0DRF.** The point space of `X = U/R` is irreducible: the closure of `x₀` is all of
it. -/
@[stacks 0DRF "the second counterexample: |X| is irreducible"]
theorem irreducibleSpace_points_infiniteProductQuotient :
    IrreducibleSpace (Space.points B (base K) hS (quotient K B hS hU hR)) :=
  have h : IsIrreducible (Set.univ :
      Set (Space.points B (base K) hS (quotient K B hS hU hR))) := by
    rw [← isGenericPoint_quotientCoordinatePoint K B hS hU hR]
    exact isIrreducible_singleton.closure
  { isPreirreducible_univ := h.2, toNonempty := ⟨h.1.choose⟩ }

omit [Finite K] in
/-- **Stacks 02Z8.** Two points of `|U|` with the same image in `|X|` are equal unless both are
coordinate points: a point of `|R|` above the pair lies either on the summand `U`, where the two
projections agree, or on the summand indexed by `(n, m)`, where the two projections are the
`n`-th and the `m`-th coordinate points of `U`. -/
theorem eq_or_coordinate_of_pointsMap_quotientMap_eq
    (u v : Space.points B (base K) hS (yoneda.obj (spaceChart K B hS hU)))
    (huv : Space.pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
        (Space.quotientMap B (base K) hS (chartSource K B hS hU hR)
          (chartTarget K B hS hU hR)) u =
      Space.pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
        (Space.quotientMap B (base K) hS (chartSource K B hS hU hR)
          (chartTarget K B hS hU hR)) v) :
    u = v ∨ ((∃ n, u = coordinateChartPoint K B hS hU n) ∧
      ∃ m, v = coordinateChartPoint K B hS hU m) := by
  obtain ⟨r, hrt, hrs⟩ :=
    (Space.Presentation.pointsRelation_iff (presentation K B hS hU hR) u v).mpr huv
  have hrt' : Space.pointsMap B (base K) hS (yoneda.obj (relationChart K B hS hR))
      (yoneda.map (chartTarget K B hS hU hR)) r = u := hrt
  have hrs' : Space.pointsMap B (base K) hS (yoneda.obj (relationChart K B hS hR))
      (yoneda.map (chartSource K B hS hU hR)) r = v := hrs
  set w : (relation K : Type u) :=
    Space.schemePointsHomeomorph B (base K) hS (relationChart K B hS hR) r with hw
  have hu : u = (Space.schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm
      ((relationTarget K).base w) := by
    rw [← hrt', Space.pointsMap_yoneda_eq_conj, toScheme_map_chartTarget]
    rfl
  have hv : v = (Space.schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm
      ((relationSource K).base w) := by
    rw [← hrs', Space.pointsMap_yoneda_eq_conj, toScheme_map_chartSource]
    rfl
  obtain ⟨i, y, hy⟩ := (sigmaOpenCover (relationComponent K)).exists_eq w
  have hyι : (Sigma.ι (relationComponent K) i).base y = w := hy
  have hcomp : ∀ m : relation K ⟶ space K,
      m.base w = (Sigma.ι (relationComponent K) i ≫ m).base y := by
    intro m
    rw [← hyι]
    exact (Scheme.Hom.comp_apply _ _ _).symm
  cases i with
  | inl j =>
    refine Or.inl ?_
    have hts : (relationTarget K).base w = (relationSource K).base w := by
      rw [hcomp (relationTarget K), hcomp (relationSource K), ι_inl_relationTarget,
        ι_inl_relationSource]
    rw [hu, hv, hts]
  | inr p =>
    have hysub : Subsingleton ((sigmaOpenCover (relationComponent K)).X (Sum.inr p)) :=
      inferInstanceAs (Subsingleton (base K : Type u))
    have hydef : y = (default : base K) := Subsingleton.elim _ _
    refine Or.inr ⟨⟨p.1.1, ?_⟩, ⟨p.1.2, ?_⟩⟩
    · have ht : (relationTarget K).base w = (coordinate K p.1.1).base (default : base K) := by
        rw [hcomp (relationTarget K), ι_inr_relationTarget, hydef]
      rw [hu, ht, coordinateChartPoint]
    · have hsrc : (relationSource K).base w = (coordinate K p.1.2).base (default : base K) := by
        rw [hcomp (relationSource K), ι_inr_relationSource, hydef]
      rw [hv, hsrc, coordinateChartPoint]

omit [Finite K] in
/-- A point of `|X|` other than `x₀` has at most one preimage in `|U|`: two points of `|U|` with
that image are equal, since otherwise both would be coordinate points and the common image would
be `x₀`. -/
theorem subsingleton_preimage_of_ne
    (z : Space.points B (base K) hS (quotient K B hS hU hR))
    (hz : z ≠ quotientCoordinatePoint K B hS hU hR) :
    (Space.pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
      (Space.quotientMap B (base K) hS (chartSource K B hS hU hR)
        (chartTarget K B hS hU hR)) ⁻¹' {z}).Subsingleton := by
  intro a ha b hb
  rw [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
  rcases eq_or_coordinate_of_pointsMap_quotientMap_eq K B hS hU hR a b (ha.trans hb.symm) with
    h | ⟨⟨n, rfl⟩, -⟩
  · exact h
  · exact absurd
      (((pointsMap_quotientMap_coordinateChartPoint K B hS hU hR n).symm.trans ha).symm) hz

/-- Every point of `|X|` other than `x₀` is closed: its preimage in `|U|` is a single point,
closed because `|U|` is `T₁`, and `|U| → |X|` is a quotient map. -/
theorem isClosed_singleton_of_ne
    (z : Space.points B (base K) hS (quotient K B hS hU hR))
    (hz : z ≠ quotientCoordinatePoint K B hS hU hR) :
    IsClosed ({z} : Set (Space.points B (base K) hS (quotient K B hS hU hR))) := by
  have hsurj := surjective_pointsMap_quotientMap K B hS hU hR
  have hquot := Space.isQuotientMap_pointsMap_of_presheafEtale B (base K) hS
    (Space.quotientMap B (base K) hS (chartSource K B hS hU hR) (chartTarget K B hS hU hR))
    (quotientMap_etale K B hS hU hR) hsurj
  have ht1 := t1Space_points_spaceChart K B hS hU
  obtain ⟨c, hc⟩ := hsurj z
  rw [← hquot.isCoinducing.isClosed_preimage,
    (subsingleton_preimage_of_ne K B hS hU hR z hz).eq_singleton_of_mem
      (show c ∈ _ from by rw [Set.mem_preimage, hc]; rfl)]
  exact isClosed_singleton

/-- The point space of `X = U/R` is Kolmogorov: all of its points except `x₀` are closed, so of
two distinct points at least one spans a closed singleton not containing the other. -/
theorem t0Space_points_infiniteProductQuotient :
    T0Space (Space.points B (base K) hS (quotient K B hS hU hR)) := by
  have key : ∀ a b : Space.points B (base K) hS (quotient K B hS hU hR),
      a ≠ quotientCoordinatePoint K B hS hU hR → Inseparable a b → a = b := by
    intro a b ha hab
    have hbe : b ∈ closure ({a} : Set _) := by
      rw [inseparable_iff_closure_eq.mp hab]
      exact subset_closure rfl
    rwa [(isClosed_singleton_of_ne K B hS hU hR a ha).closure_eq, Set.mem_singleton_iff,
      eq_comm] at hbe
  refine ⟨fun a b hab ↦ ?_⟩
  by_cases ha : a = quotientCoordinatePoint K B hS hU hR
  · by_cases hb : b = quotientCoordinatePoint K B hS hU hR
    · rw [ha, hb]
    · exact (key b a hb hab.symm).symm
  · exact key a b ha hab

omit [Finite K] in
/-- There is a point of `|X|` other than `x₀`: the spectrum of `∏ n : ℕ, K` has a point coming
from no coordinate projection, and the image of such a point is not `x₀`. -/
theorem exists_ne_quotientCoordinatePoint :
    ∃ z : Space.points B (base K) hS (quotient K B hS hU hR),
      z ≠ quotientCoordinatePoint K B hS hU hR := by
  obtain ⟨x, hx⟩ := Space.InfiniteProduct.exists_noncoordinate_point K
  refine ⟨Space.pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
    (Space.quotientMap B (base K) hS (chartSource K B hS hU hR) (chartTarget K B hS hU hR))
    ((Space.schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm x), ?_⟩
  intro hcon
  obtain ⟨n, hn⟩ : ∃ n, (Space.schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm x =
      coordinateChartPoint K B hS hU n := by
    rcases eq_or_coordinate_of_pointsMap_quotientMap_eq K B hS hU hR _
        (coordinateChartPoint K B hS hU 0)
        (hcon.trans (pointsMap_quotientMap_coordinateChartPoint K B hS hU hR 0).symm) with
      h | ⟨⟨n, hn⟩, -⟩
    exacts [⟨0, h⟩, ⟨n, hn⟩]
  exact hx n ((Space.schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm.injective hn)

/-- Every irreducible closed subset of `|X|` is minimal or maximal: one containing `x₀` is all of
`|X|`, the closure of `x₀` being everything, and one avoiding `x₀` is minimal, because its
preimage in `|U|` is irreducible — the fibres of `|U| → |X|` over its points are single points and
the map is open — while `|U|` has no strict chain of irreducible closed subsets. -/
theorem isMin_or_isMax_irreducibleCloseds_points :
    ∀ Z : TopologicalSpace.IrreducibleCloseds
      (Space.points B (base K) hS (quotient K B hS hU hR)), IsMin Z ∨ IsMax Z := by
  intro Z
  by_cases hx₀ : quotientCoordinatePoint K B hS hU hR ∈ Z.carrier
  · refine Or.inr fun W hZW ↦ ?_
    have huniv : Z.carrier = Set.univ := by
      refine Set.eq_univ_of_univ_subset ?_
      rw [← isGenericPoint_quotientCoordinatePoint K B hS hU hR]
      exact Z.isClosed'.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hx₀)
    change W.carrier ⊆ Z.carrier
    rw [huniv]
    exact Set.subset_univ _
  · refine Or.inl fun W hWZ ↦ ?_
    set f := Space.pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
      (Space.quotientMap B (base K) hS (chartSource K B hS hU hR) (chartTarget K B hS hU hR))
    have hsurj : Function.Surjective f := surjective_pointsMap_quotientMap K B hS hU hR
    have hcont : Continuous f := Space.continuous_pointsMap B (base K) hS _
    have hopen : IsOpenMap f := Space.isOpenMap_pointsMap_of_presheafEtale B (base K) hS _
      (quotientMap_etale K B hS hU hR)
    have hpre : ∀ Y : TopologicalSpace.IrreducibleCloseds
        (Space.points B (base K) hS (quotient K B hS hU hR)),
        Y.carrier ⊆ Z.carrier → IsIrreducible (f ⁻¹' Y.carrier) := by
      intro Y hYZ
      obtain ⟨y, hy⟩ := Y.isIrreducible'.nonempty
      obtain ⟨c, hc⟩ := hsurj y
      refine ⟨⟨c, show c ∈ _ from by rw [Set.mem_preimage, hc]; exact hy⟩, ?_⟩
      refine Y.isIrreducible'.isPreirreducible.preimage_of_dense_isPreirreducible_fiber _
        hopen ?_
      refine Set.Subset.trans (Set.subset_inter (subset_refl _) fun y' hy' ↦ ?_) subset_closure
      exact (subsingleton_preimage_of_ne K B hS hU hR y'
        (fun h ↦ hx₀ (h ▸ hYZ hy'))).isPreirreducible
    have hdim0 : Order.krullDim (TopologicalSpace.IrreducibleCloseds
        (Space.points B (base K) hS (yoneda.obj (spaceChart K B hS hU)))) ≤ 0 :=
      topologicalKrullDim_points_spaceChart_le_zero K B hS hU
    have hWZ' : W.carrier ⊆ Z.carrier := hWZ
    have hmax := Order.krullDim_nonpos_iff_forall_isMax.mp hdim0
      (⟨_, hpre W hWZ', W.isClosed'.preimage hcont⟩ : TopologicalSpace.IrreducibleCloseds _)
    have hle : f ⁻¹' Z.carrier ⊆ f ⁻¹' W.carrier :=
      hmax (b := (⟨_, hpre Z (subset_refl _), Z.isClosed'.preimage hcont⟩ :
        TopologicalSpace.IrreducibleCloseds _))
        (Set.preimage_mono hWZ' : f ⁻¹' W.carrier ⊆ f ⁻¹' Z.carrier)
    change Z.carrier ⊆ W.carrier
    intro z hz
    obtain ⟨c, rfl⟩ := hsurj z
    exact hle hz

/-- **Stacks 0DRF.** The point space of `X = U/R` is of Krull dimension `1`: it is irreducible
with generic point `x₀`, and every irreducible closed subset of it is either all of it or a single
point. -/
@[stacks 0DRF "the second counterexample: |X| is of Krull dimension 1"]
theorem topologicalKrullDim_points_infiniteProductQuotient_eq_one :
    topologicalKrullDim (Space.points B (base K) hS (quotient K B hS hU hR)) = 1 := by
  have hle1 : Order.krullDim (TopologicalSpace.IrreducibleCloseds
      (Space.points B (base K) hS (quotient K B hS hU hR))) ≤ 1 :=
    Order.krullDim_le_one_iff.mpr (isMin_or_isMax_irreducibleCloseds_points K B hS hU hR)
  refine le_antisymm hle1 ?_
  have := t0Space_points_infiniteProductQuotient K B hS hU hR
  obtain ⟨z, hz⟩ := exists_ne_quotientCoordinatePoint K B hS hU hR
  refine one_le_topologicalKrullDim_of_specializes_of_ne
    (x := quotientCoordinatePoint K B hS hU hR) (y := z) ?_ (Ne.symm hz)
  rw [specializes_iff_mem_closure, isGenericPoint_quotientCoordinatePoint K B hS hU hR]
  trivial

/-- **Stacks 0DRF.** The local Krull dimension of the point space of `X = U/R` is `1` at every
point other than `x₀`: every open neighbourhood of such a point contains `x₀` as well, whose
closure is everything, so the point and the neighbourhood form a chain of length one. -/
@[stacks 0DRF "the second counterexample: the local dimension of |X| is 1 at each of its points \
  other than x₀"]
theorem topologicalKrullDimAt_points_infiniteProductQuotient_eq_one
    (z : Space.points B (base K) hS (quotient K B hS hU hR))
    (hz : z ≠ quotientCoordinatePoint K B hS hU hR) :
    topologicalKrullDimAt (Space.points B (base K) hS (quotient K B hS hU hR)) z = 1 := by
  have ht0 := t0Space_points_infiniteProductQuotient K B hS hU hR
  refine le_antisymm ((topologicalKrullDimAt_le_topologicalKrullDim z).trans
    (le_of_eq (topologicalKrullDim_points_infiniteProductQuotient_eq_one K B hS hU hR))) ?_
  obtain ⟨⟨V, hzV, hV, hdim⟩, -⟩ := topologicalKrullDimAt_isLeast
    (Space.points B (base K) hS (quotient K B hS hU hR)) z
  rw [hdim]
  have hdense : Dense ({quotientCoordinatePoint K B hS hU hR} :
      Set (Space.points B (base K) hS (quotient K B hS hU hR))) :=
    dense_iff_closure_eq.mpr (isGenericPoint_quotientCoordinatePoint K B hS hU hR)
  obtain ⟨c, hcV, hc⟩ := hdense.inter_open_nonempty V hV ⟨z, hzV⟩
  rw [Set.mem_singleton_iff] at hc
  subst hc
  refine one_le_topologicalKrullDim_of_specializes_of_ne
    (x := (⟨quotientCoordinatePoint K B hS hU hR, hcV⟩ : ↥V)) (y := (⟨z, hzV⟩ : ↥V)) ?_ ?_
  · rw [subtype_specializes_iff, specializes_iff_mem_closure,
      isGenericPoint_quotientCoordinatePoint K B hS hU hR]
    trivial
  · exact fun h ↦ hz (congrArg Subtype.val h).symm

/-- **Stacks 0DRF.** The dimension of an algebraic space at a point can also be *smaller* than
the dimension of its point space at that point: the space `X = U/R` of Stacks 02Z8 is of
dimension `0` at each of its points, while the local Krull dimension of `|X|` is `1` at every
point other than `x₀`. -/
@[stacks 0DRF "the second counterexample: the dimension at a point is smaller than the local \
  dimension of the point space"]
theorem dimensionAtPoint_ne_topologicalKrullDimAt_points_infiniteProductQuotient
    (z : Space.points B (base K) hS (quotient K B hS hU hR))
    (hz : z ≠ quotientCoordinatePoint K B hS hU hR) :
    Space.dimensionAtPoint B (base K) hS (quotient K B hS hU hR)
        (isAlgebraicSpace_quotient K B hS hU hR) z ≠
      topologicalKrullDimAt (Space.points B (base K) hS (quotient K B hS hU hR)) z := by
  rw [dimensionAtPoint_infiniteProductQuotient_eq_zero K B hS hU hR z,
    topologicalKrullDimAt_points_infiniteProductQuotient_eq_one K B hS hU hR z hz]
  simp

omit [Finite K] in
/-- **Stacks 0DRF is inaccurate at the generic point.** The remark says of the example of
Stacks 02Z8 that `|X|` admitting a generic point makes "the dimension of `|X|` at any of its
points" equal to `1`. That fails at the generic point `x₀` itself: the coordinate points form an
open subset of `|U|`, saturated for the relation, and `|U| → |X|` is open, so `{x₀}` is an open
neighbourhood of `x₀` of Krull dimension `0`. At `x₀` the two dimensions compared by the remark
therefore agree, both being `0`; the example separates them at every other point. -/
@[stacks 0DRF "the second counterexample, corrected: at x₀ the local dimension of |X| is 0, not 1"]
theorem topologicalKrullDimAt_quotientCoordinatePoint_eq_zero :
    topologicalKrullDimAt (Space.points B (base K) hS (quotient K B hS hU hR))
      (quotientCoordinatePoint K B hS hU hR) = 0 := by
  refine topologicalKrullDimAt_eq_zero_of_isIsolatedPoint _ ?_
  set f := Space.pointsMap B (base K) hS (yoneda.obj (spaceChart K B hS hU))
    (Space.quotientMap B (base K) hS (chartSource K B hS hU hR) (chartTarget K B hS hU hR))
  have hopen : IsOpenMap f := Space.isOpenMap_pointsMap_of_presheafEtale B (base K) hS _
    (quotientMap_etale K B hS hU hR)
  have himage : f '' (⋃ n : ℕ, {coordinateChartPoint K B hS hU n}) =
      {quotientCoordinatePoint K B hS hU hR} := by
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp ha
      rw [Set.mem_singleton_iff, Set.mem_singleton_iff.mp hn]
      exact pointsMap_quotientMap_coordinateChartPoint K B hS hU hR n
    · intro t ht
      rw [Set.mem_singleton_iff] at ht
      subst ht
      exact ⟨coordinateChartPoint K B hS hU 0, Set.mem_iUnion.mpr ⟨0, rfl⟩,
        pointsMap_quotientMap_coordinateChartPoint K B hS hU hR 0⟩
  rw [isIsolatedPoint_iff, ← himage]
  refine hopen _ (isOpen_iUnion fun n ↦ ?_)
  have heq : (Space.schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm ''
      {(coordinate K n).base (default : base K)} =
      ({coordinateChartPoint K B hS hU n} :
        Set (Space.points B (base K) hS (yoneda.obj (spaceChart K B hS hU)))) :=
    Set.image_singleton
  rw [← heq]
  exact (Space.schemePointsHomeomorph B (base K) hS (spaceChart K B hS hU)).symm.isOpenMap _
    ((Space.InfiniteProduct.isOpen_singleton_iff_coordinate K _).mpr ⟨n, rfl⟩)

end Quotient

end SecondExample

/-! ### The second example, with no parameters left -/

section SecondExampleExists

open AlgebraicGeometry.Space.InfiniteProduct

/-- **Stacks 0DRF.** There is an algebraic space over a field which is of dimension `0` at each
of its points while its point space is irreducible of Krull dimension `1` and admits a generic
point: the example of Stacks 02Z8 over the field with two elements, on a big fppf site
containing the three schemes it is built from. -/
@[stacks 0DRF "the second counterexample exists: an algebraic space of dimension 0 at each of \
  its points whose point space is irreducible of Krull dimension 1 with a generic point"]
theorem exists_dimensionAtPoint_eq_zero_topologicalKrullDim_points_eq_one :
    ∃ (B : BigFppfSite.{u}) (hS : B.Contains (base (ULift.{u} (ZMod 2))))
      (F : (BigFppfOver B (base (ULift.{u} (ZMod 2))) hS)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B (base (ULift.{u} (ZMod 2))) hS F),
      (∀ x, Space.dimensionAtPoint B (base (ULift.{u} (ZMod 2))) hS F hF x = 0) ∧
        IrreducibleSpace (Space.points B (base (ULift.{u} (ZMod 2))) hS F) ∧
        topologicalKrullDim (Space.points B (base (ULift.{u} (ZMod 2))) hS F) = 1 ∧
        ∃ x₀, IsGenericPoint x₀
          (Set.univ : Set (Space.points B (base (ULift.{u} (ZMod 2))) hS F)) := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing
    ({base (ULift.{u} (ZMod 2)), space (ULift.{u} (ZMod 2)),
      relation (ULift.{u} (ZMod 2))} : Set Scheme.{u})
  have hS : B.Contains (base (ULift.{u} (ZMod 2))) := hB _ (by simp)
  have hU : B.Contains (space (ULift.{u} (ZMod 2))) := hB _ (by simp)
  have hR : B.Contains (relation (ULift.{u} (ZMod 2))) := hB _ (by simp)
  let := BigFppfOver.hasSheafify_type B (base (ULift.{u} (ZMod 2))) hS
  exact ⟨B, hS, quotient (ULift.{u} (ZMod 2)) B hS hU hR,
    isAlgebraicSpace_quotient (ULift.{u} (ZMod 2)) B hS hU hR,
    dimensionAtPoint_infiniteProductQuotient_eq_zero (ULift.{u} (ZMod 2)) B hS hU hR,
    irreducibleSpace_points_infiniteProductQuotient (ULift.{u} (ZMod 2)) B hS hU hR,
    topologicalKrullDim_points_infiniteProductQuotient_eq_one (ULift.{u} (ZMod 2)) B hS hU hR,
    ⟨quotientCoordinatePoint (ULift.{u} (ZMod 2)) B hS hU hR,
      isGenericPoint_quotientCoordinatePoint (ULift.{u} (ZMod 2)) B hS hU hR⟩⟩

end SecondExampleExists

end Stacks.Examples.DimensionVersusPointSet

end
