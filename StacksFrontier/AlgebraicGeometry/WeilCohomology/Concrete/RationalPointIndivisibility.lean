module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ClosedImmersionClass
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.GysinOpenImmersion
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.ScalarExtension
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZeroSplitting
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DisjointUnionIso
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.DimensionZero
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPointDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.RelativeDimensionCongr
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroCyclesSeparablePointsBertini

/-!
# Differences of classes of rational points are indivisible (Stacks 0FHU)

Assume given data (D0)–(D3) satisfying (A), (B), (C) over the actual category of smooth
projective schemes over `k` (`Stacks.WeilCohomology.WeilData`). Let `k'/k` be a finite separable
extension, `X` smooth projective over `k'`, and `x, x'` two `k'`-rational points of `X`. Stacks
0FHU: if `γ(x) ≠ γ(x')`, then `[x] - [x']` is divisible by no integer `n > 1` in `CH_0(X)`.

The proof is the source's, on the actual objects.

* If `x` and `x'` lie in different parts of `X` of constant dimension, the degree of a zero cycle
  on the part containing `x` is one on `[x] - [x']`
  (`Stacks.WeilCohomology.rationalPointChowClass_sub_ne_zsmul_of_mem_of_notMem`).
* Otherwise restrict to that part `Y = X_d`, equidimensional of dimension `d`. There
  (`WeilData.cycleClass_eq_of_sub_eq_zsmul_of_equidimensional`): by Stacks 0FH5 every class of
  `CH_0(Y)` is an integral combination of classes of closed points `y` with separable residue
  field; `Spec κ(y)` is a smooth projective `k`-scheme of dimension zero and by Stacks 0FHG and
  Stacks 0FHQ (2), (4) the functional `a ↦ ∫_Y a ∪ γ([y])` on `H^0(Y)` is the trace of the finite
  separable `F`-algebra `H^0(κ(y))` composed with the pullback. The divisibility then gives the
  trace relation of Stacks 0FHT between the pullbacks along the two points, which are split by the
  pullback along `Y ⟶ Spec k'`; so they agree, and by Poincaré duality (A)(b)
  `γ([x]) = γ([x'])` in `H^{2d}(Y)(d)`.
* Back on `X = Y ⨿ (X ∖ Y)`: by (C)(a), the Gysin map of an open immersion being restriction
  (`Stacks.WeilCohomology.codimensionGysin_of_isOpenImmersion`), the pullbacks of `γ([x])` and
  `γ([x'])` to the two summands agree, hence so do the classes (Stacks 0FHJ); in the other
  codimensions both classes vanish.

## Main definitions

* `Stacks.WeilCohomology.ofOverField`: a smooth projective scheme over `k'` as one over `k`.
* `Stacks.WeilCohomology.rationalPointClass`: the class `[x] ∈ CH^i(X)` of a rational point.
* `Stacks.WeilCohomology.zeroCycleToCodimension`: `CH_0(X) ⟶ CH^i(X)`.
* `Stacks.WeilCohomology.closedPointObj`: a closed point with separable residue field as the
  smooth projective `k`-scheme `Spec κ(y)`.
* `Stacks.WeilCohomology.WeilData.h0Pairing`: the pairing `H^0(X) × H^{2d}(X)(d) ⟶ F`.

## Main results

* `Stacks.WeilCohomology.WeilData.rationalPointChowClass_sub_ne_zsmul`: **Stacks 0FHU**.
* `Stacks.WeilCohomology.WeilData.cycleClass_eq_of_sub_eq_zsmul_of_equidimensional`: the
  equidimensional case.
* `Stacks.WeilCohomology.WeilData.h0Pairing_cycleClass_closedSubschemeClass`:
  `∫_Y a ∪ γ([Z]) = Tr_{H^0(Z)/F}(i^*a)` for `Z` of dimension zero.
* `Stacks.WeilCohomology.WeilData.eq_of_pullTw_eq_of_isColimit`: Stacks 0FHJ, injectivity, on
  twisted cohomology.

## Implementation notes

The source writes `γ(x)` for the cohomology class of the zero cycle `[x]`. For `X` not
equidimensional that class lives in `H^{2d}(X)(d)` for `d` the dimension of `X` at `x`, which
depends on the point; it is stated here as the family of the classes `γ([x]) ∈ H^{2i}(X)(i)` of
`[x] ∈ CH^i(X)` in every codimension `i`, all of which vanish but the one at `i = d`. The
divisibility is in the Chow group of `X` over `k'`, as in the source, and is compared with
classes over `k` through `Stacks.Chow.chowGroupFiniteExtensionEquiv`.

## References

* [Stacks Project, Tag 0FHU](https://stacks.math.columbia.edu/tag/0FHU)
* [Stacks Project, Tag 0FH5](https://stacks.math.columbia.edu/tag/0FH5)
* [Stacks Project, Tag 0FHT](https://stacks.math.columbia.edu/tag/0FHT)
* [Stacks Project, Tag 0FHQ](https://stacks.math.columbia.edu/tag/0FHQ)
* [Stacks Project, Tag 0FHG](https://stacks.math.columbia.edu/tag/0FHG)
* [Stacks Project, Tag 0FHJ](https://stacks.math.columbia.edu/tag/0FHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.Chow

universe u w

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k]

/-! ### Zero cycles as classes graded by codimension -/

section ZeroCycles

variable {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX]

/-- **A zero cycle class as a class of codimension `i`**: `CH_0(X) = ∏_e CH_0(X_e)`, and
`CH_0(X_e) = CH_{e-e}(X_e)` is the part of `CH^i(X) = ∏_e CH_{e-i}(X_e)` at `e = i`; the other
parts of a zero cycle class in `CH^i(X)` are zero. -/
def zeroCycleToCodimension (i : ℤ) :
    chowGroup (fieldChowSituation k) sX 0 →+ codimensionChowGroup k sX i :=
  AddMonoidHom.pi fun e : ℕ ↦
    if h : (0 : ℤ) = e - i then
      (chowGroupDegreeEquiv _ _ h).toAddMonoidHom.comp
        (chowGroupRestrict (fieldChowSituation k) sX (partBase sX e) (dimPart sX e).ι rfl 0)
    else 0

omit [Smooth sX] in
/-- The cycle of a closed subscheme of dimension zero vanishes in nonzero dimension. -/
theorem cycleAssociatedToClosedSubscheme_eq_zero_of_ne [LocallyOfFiniteType sX] {Z : Scheme.{u}}
    (i : Z ⟶ X)
    [IsClosedImmersion i]
    (hZ : ∀ z : Z, relativeDimension (fieldChowSituation k).dimensionFunction (i ≫ sX) z = 0)
    {n : ℤ} (hn : n ≠ 0) :
    cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX i n = 0 := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun x ↦ ?_)
  refine cycleAssociatedToClosedSubscheme_apply_eq_zero _ sX i n x ?_
  rintro ⟨ξ, rfl, hξ⟩
  rw [← relativeDimension_comp_closedImmersion, hZ] at hξ
  exact hn hξ.symm

/-- **The class of a closed subscheme of dimension zero**, read in codimension `i`, is the class
`[Z] ∈ CH^i(X)` of the closed subscheme. -/
theorem zeroCycleToCodimension_mk_cycleAssociatedToClosedSubscheme {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (hZ : ∀ z : Z, relativeDimension (fieldChowSituation k).dimensionFunction (i ≫ sX) z = 0)
    (c : ℤ) :
    zeroCycleToCodimension sX c
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX i 0)) =
      closedSubschemeClass sX i c := by
  funext e
  simp only [zeroCycleToCodimension, AddMonoidHom.pi_apply, closedSubschemeClass_apply]
  by_cases h : (0 : ℤ) = e - c
  · rw [dite_eq_left h]
    refine eq_of_heq ((chowGroupDegreeEquiv_heq _ _ _ _).trans
      (chowGroupRestrict_heq_of_eq (fieldChowSituation k) (dimPart sX e).ι (dimPart sX e).ι rfl rfl
        rfl rfl rfl h _ _
        (Stacks.Chow.mk_cycleAssociatedToClosedSubscheme_heq (fieldChowSituation k) sX i h)))
  · rw [dite_eq_right h, cycleAssociatedToClosedSubscheme_eq_zero_of_ne sX i hZ (Ne.symm h)]
    exact (map_zero _).symm

/-- **Two integral closed subschemes with the same generic point have the same cycle.** -/
theorem cycleAssociatedToClosedSubscheme_eq_of_genericPoint_eq (C : ChowSituation.{u})
    {T Z Z' : Scheme.{u}} (sT : T ⟶ C.S) [LocallyOfFiniteType sT] (i : Z ⟶ T)
    [IsClosedImmersion i] (i' : Z' ⟶ T) [IsClosedImmersion i'] [IsIntegral Z] [IsIntegral Z']
    (h : i (genericPoint Z) = i' (genericPoint Z')) (n : ℤ) :
    cycleAssociatedToClosedSubscheme C sT i n = cycleAssociatedToClosedSubscheme C sT i' n := by
  have hZ := genericPoint_mem_genericPoints Z
  have hZ' := genericPoint_mem_genericPoints Z'
  have hgen : ∀ (W : Scheme.{u}) [IsIntegral W] (ξ : genericPoints W),
      ξ.1 = genericPoint W := fun W _ ξ ↦ by
    have hmem : (ξ : W) ∈ ({genericPoint W} : Set W) := by
      rw [← genericPoints_eq_singleton]; exact ξ.2
    exact hmem
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  by_cases hy : y = i (genericPoint Z) ∧ relativeDimension C.dimensionFunction sT y = n
  · obtain ⟨rfl, hn⟩ := hy
    rw [cycleAssociatedToClosedSubscheme_apply C sT i n ⟨_, hZ⟩ hn,
      componentMultiplicity_eq_one i hZ]
    rw [h] at hn ⊢
    rw [cycleAssociatedToClosedSubscheme_apply C sT i' n ⟨_, hZ'⟩ hn,
      componentMultiplicity_eq_one i' hZ']
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero,
      cycleAssociatedToClosedSubscheme_apply_eq_zero]
    · rintro ⟨ξ, hξ, hn⟩
      exact hy ⟨by rw [← hξ, hgen Z' ξ, h], hn⟩
    · rintro ⟨ξ, hξ, hn⟩
      exact hy ⟨by rw [← hξ, hgen Z ξ], hn⟩

end ZeroCycles

/-! ### Points as smooth projective schemes of dimension zero -/

section Points

open SmoothProjectiveScheme

/-- A finite separable field extension is étale. -/
theorem etale_of_isSeparable (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L]
    [Algebra.IsSeparable k L] : Algebra.Etale k L :=
  ⟨Algebra.FormallyEtale.of_isSeparable k L,
    Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩

/-- The spectrum of a field has dimension zero. -/
theorem topologicalKrullDim_spec_field (L : Type u) [Field L] :
    topologicalKrullDim (Spec (.of L)) = 0 := by
  have : Unique (Spec (.of L)) := inferInstanceAs (Unique (PrimeSpectrum L))
  refine le_antisymm (topologicalKrullDim_zero_of_discreteTopology _) ?_
  have : Nonempty (TopologicalSpace.IrreducibleCloseds (Spec (.of L))) :=
    ⟨⟨closure {default}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
  exact Order.krullDim_nonneg

variable (L : Type u) [Field L] [Algebra k L] [FiniteDimensional k L] [Algebra.IsSeparable k L]

/-- **The spectrum of a finite separable extension `L/k`**, a smooth projective `k`-scheme of
dimension zero. -/
abbrev specField : (SmoothProjectiveScheme k).FullSubcategory :=
  haveI := etale_of_isSeparable (k := k) L
  spec k L

/-- `Spec L` is nonempty and equidimensional of dimension zero. -/
theorem isNonemptyEquidimensional_specField :
    IsNonemptyEquidimensional (specField (k := k) L) 0 :=
  isNonemptyEquidimensional_of_dimension_zero (topologicalKrullDim_spec_field L)

variable {L}

/-- A morphism `Spec L ⟶ Y` over `k` as a morphism of smooth projective `k`-schemes. -/
def specFieldHom {Y : (SmoothProjectiveScheme k).FullSubcategory} (y : Spec (.of L) ⟶ Y.obj.left)
    (hy : y ≫ Y.obj.hom = specStructure k L) : specField (k := k) L ⟶ Y :=
  ObjectProperty.homMk (Over.homMk y hy)

/-- The underlying morphism of schemes of `specFieldHom y hy` is `y`. -/
@[simp]
theorem specFieldHom_left {Y : (SmoothProjectiveScheme k).FullSubcategory}
    (y : Spec (.of L) ⟶ Y.obj.left)
    (hy : y ≫ Y.obj.hom = specStructure k L) : (specFieldHom y hy).hom.left = y :=
  rfl

/-! ### Closed points with separable residue field -/

section ClosedPoint

variable {Y : (SmoothProjectiveScheme k).FullSubcategory} (y : Y.obj.left)

/-- The `k`-algebra structure of the residue field at a point of a scheme over `k`. -/
abbrev residueFieldAlgebra : Algebra k (Y.obj.left.residueField y) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ Y.obj.hom.appTop ≫ Y.obj.left.Γevaluation y).hom.toAlgebra

/-- The inclusion `Spec κ(y) ⟶ Y` followed by the structure morphism is the spectrum of the
`k`-algebra structure of `κ(y)`. -/
theorem fromSpecResidueField_comp_hom :
    Y.obj.left.fromSpecResidueField y ≫ Y.obj.hom =
      Spec.map ((Scheme.ΓSpecIso (.of k)).inv ≫ Y.obj.hom.appTop ≫ Y.obj.left.Γevaluation y) := by
  rw [← Y.obj.hom.SpecMap_residueFieldMap_fromSpecResidueField y]
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, ← Spec.map_comp]
  congr 1
  rw [← Scheme.Γevaluation_naturality]
  simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]

variable {y} (hy : IsClosed ({y} : Set Y.obj.left))
  (hsep : HasSeparableResidueField k Y.obj.hom y)

include hy hsep in
/-- `Spec κ(y) ⟶ Spec k` is smooth for a point with separable residue field. -/
theorem smooth_fromSpecResidueField_comp :
    Smooth (Y.obj.left.fromSpecResidueField y ≫ Y.obj.hom) := by
  let := residueFieldAlgebra y
  have : Module.Finite k (Y.obj.left.residueField y) :=
    residueField_finite_of_closed_point k Y.obj.hom y hy
  have : Algebra.IsSeparable k (Y.obj.left.residueField y) := hsep
  have := etale_of_isSeparable (k := k) (Y.obj.left.residueField y)
  rw [fromSpecResidueField_comp_hom, HasRingHomProperty.Spec_iff (P := @Smooth)]
  exact RingHom.smooth_algebraMap.mpr inferInstance

/-- **The closed point `y` as a smooth projective `k`-scheme** `Spec κ(y)`, for `y` closed with
residue field separable over `k`. -/
def closedPointObj : (SmoothProjectiveScheme k).FullSubcategory :=
  haveI : IsClosedImmersion (Y.obj.left.fromSpecResidueField y) :=
    isClosed_singleton_iff_isClosedImmersion.mp hy
  ⟨Over.mk (Y.obj.left.fromSpecResidueField y ≫ Y.obj.hom),
    smooth_fromSpecResidueField_comp hy hsep,
    IsProjectiveMorphism.isProjective <| by
      obtain ⟨n, j, hj, h⟩ :=
          ((isProjective_iff_isProjectiveMorphism_of_isAffine _).1
          (SmoothProjectiveScheme.isProjective Y))
      exact ⟨n, Y.obj.left.fromSpecResidueField y ≫ j, inferInstance, by
        rw [Category.assoc, h]; rfl⟩⟩

/-- The inclusion `Spec κ(y) ⟶ Y` of a closed point. -/
def closedPointHom : closedPointObj hy hsep ⟶ Y :=
  ObjectProperty.homMk (Over.homMk (Y.obj.left.fromSpecResidueField y) rfl)

/-- The underlying morphism of schemes of `closedPointHom` is `Spec κ(y) ⟶ Y`. -/
@[simp]
theorem closedPointHom_left :
    (closedPointHom hy hsep).hom.left = Y.obj.left.fromSpecResidueField y :=
  rfl

/-- The inclusion `Spec κ(y) ⟶ Y` of a closed point is a closed immersion. -/
instance : IsClosedImmersion (closedPointHom hy hsep).hom.left :=
  isClosed_singleton_iff_isClosedImmersion.mp hy

/-- `Spec κ(y)` is nonempty and equidimensional of dimension zero. -/
theorem isNonemptyEquidimensional_closedPointObj :
    IsNonemptyEquidimensional (closedPointObj hy hsep) 0 :=
  SmoothProjectiveScheme.isNonemptyEquidimensional_of_dimension_zero
    (topologicalKrullDim_spec_field (Y.obj.left.residueField y))

/-- The points of `Spec κ(y)` have relative dimension zero over `k`. -/
theorem relativeDimension_closedPointHom (z : (closedPointObj hy hsep).obj.left) :
    relativeDimension (fieldChowSituation k).dimensionFunction
      ((closedPointHom hy hsep).hom.left ≫ Y.obj.hom) z = 0 := by
  rw [relativeDimension_comp_closedImmersion]
  have hz : (closedPointHom hy hsep).hom.left z = y :=
    Scheme.fromSpecResidueField_apply (X := Y.obj.left) y z
  rw [hz]
  exact relativeDimension_eq_zero_of_isClosed (fieldChowSituation k) (fun _ _ ↦ rfl) Y.obj.hom y hy

/-- **The class of a closed point is the class of `Spec κ(y)`**: the prime cycle of `y`. -/
theorem mk_integralComponentAt_eq :
    (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) Y.obj.hom 0)
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Y.obj.hom
          (integralComponentAt y).subschemeι 0) : chowGroup (fieldChowSituation k) Y.obj.hom 0) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) Y.obj.hom
        (closedPointHom hy hsep).hom.left 0) := by
  have := isIntegral_integralComponentAt y
  have : IsIntegral (closedPointObj hy hsep).obj.left :=
    inferInstanceAs (IsIntegral (Spec (.of (Y.obj.left.residueField y))))
  refine congrArg (QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) Y.obj.hom 0))
    (cycleAssociatedToClosedSubscheme_eq_of_genericPoint_eq (fieldChowSituation k) Y.obj.hom
    (integralComponentAt y).subschemeι (closedPointHom hy hsep).hom.left ?_ 0)
  rw [show (closedPointHom hy hsep).hom.left (genericPoint (closedPointObj hy hsep).obj.left) = y
    from Scheme.fromSpecResidueField_apply (X := Y.obj.left) y _]
  exact genericPointOf_integralComponentAt y

end ClosedPoint

end Points

/-! ### Integral combinations of separable traces -/

section TraceCombination

variable {F A : Type w} [Field F] [CommRing A] [Algebra F A]

/-- The zero functional is a separable trace combination. -/
theorem IsSeparableTraceCombination.zero :
    IsSeparableTraceCombination.{w, w, w} F A 0 :=
  ⟨0, fun i ↦ PEmpty, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0, fun i ↦ i.elim0,
    fun i ↦ i.elim0, fun i ↦ i.elim0, by simp⟩

/-- The negative of a separable trace combination is a separable trace combination. -/
theorem IsSeparableTraceCombination.neg {φ : A →ₗ[F] F}
    (h : IsSeparableTraceCombination.{w, w, w} F A φ) :
    IsSeparableTraceCombination.{w, w, w} F A (-φ) := by
  obtain ⟨r, G, i1, i2, i3, i4, ι, m, hm⟩ := h
  exact ⟨r, G, i1, i2, i3, i4, ι, -m, by simp [hm, Finset.sum_neg_distrib]⟩

/-- The sum of two separable trace combinations is a separable trace combination. -/
theorem IsSeparableTraceCombination.add {φ ψ : A →ₗ[F] F}
    (hφ : IsSeparableTraceCombination.{w, w, w} F A φ)
    (hψ : IsSeparableTraceCombination.{w, w, w} F A ψ) :
    IsSeparableTraceCombination.{w, w, w} F A (φ + ψ) := by
  obtain ⟨r, G, i1, i2, i3, i4, ι, m, hm⟩ := hφ
  obtain ⟨s, G', j1, j2, j3, j4, ι', m', hm'⟩ := hψ
  let H : Fin r ⊕ Fin s → Type w := Sum.elim G G'
  let e := (finSumFinEquiv (m := r) (n := s)).symm
  let c1 : ∀ t, CommRing (H t) := fun t ↦ t.rec (fun a ↦ i1 a) (fun b ↦ j1 b)
  let c2 : ∀ t, Algebra F (H t) := fun t ↦ t.rec (fun a ↦ i2 a) (fun b ↦ j2 b)
  let c3 : ∀ t, FiniteDimensional F (H t) := fun t ↦ t.rec (fun a ↦ i3 a) (fun b ↦ j3 b)
  let c4 : ∀ t, Algebra.IsSeparable F (H t) := fun t ↦ t.rec (fun a ↦ i4 a) (fun b ↦ j4 b)
  let κ : ∀ t, A →ₐ[F] H t := fun t ↦ t.rec (fun a ↦ ι a) (fun b ↦ ι' b)
  let n : Fin r ⊕ Fin s → ℤ := Sum.elim m m'
  refine ⟨r + s, fun i ↦ H (e i), fun i ↦ c1 (e i), fun i ↦ c2 (e i), fun i ↦ c3 (e i),
    fun i ↦ c4 (e i), fun i ↦ κ (e i), fun i ↦ n (e i), ?_⟩
  rw [hm, hm']
  rw [show (∑ i : Fin (r + s), n (e i) • (Algebra.trace F (H (e i))).comp (κ (e i)).toLinearMap)
      = ∑ t : Fin r ⊕ Fin s, n t • (Algebra.trace F (H t)).comp (κ t).toLinearMap from
    Fintype.sum_equiv e _ _ (fun _ ↦ rfl), Fintype.sum_sum_type]
  rfl

/-- A single trace map of a finite separable algebra is a separable trace combination. -/
theorem IsSeparableTraceCombination.trace (G : Type w) [CommRing G] [Algebra F G]
    [FiniteDimensional F G] [Algebra.IsSeparable F G] (ι : A →ₐ[F] G) :
    IsSeparableTraceCombination.{w, w, w} F A ((Algebra.trace F G).comp ι.toLinearMap) :=
  ⟨1, fun _ ↦ G, fun _ ↦ inferInstance, fun _ ↦ inferInstance, fun _ ↦ inferInstance,
    fun _ ↦ inferInstance, fun _ ↦ ι, fun _ ↦ 1, by simp⟩

end TraceCombination

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)

/-! ### The pairing of `H^0` with the top cohomology -/

/-- The degree-zero part as a linear equivalence with `H^0(X)`. -/
def h0GradeEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) : W.H0 X ≃ₗ[F] W.grade X 0 where
  toFun a := ⟨a.1, a.2⟩
  invFun b := ⟨b.1, b.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

/-- `H^0(X) ≃ H^0(X)(0)`: the degree-zero subalgebra, as the twist by `F(0)` of the degree-zero
part, through the coordinate of the twisted cup product. -/
def h0TwEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) : W.H0 X ≃ₗ[F] W.Tw X 0 0 :=
  (W.h0GradeEquiv X).trans (W.twCoord X 0 0).symm

/-- The coordinate of `h0TwEquiv X a` is `a`, as an element of `H(X)`. -/
theorem twCoord_h0TwEquiv (X : (SmoothProjectiveScheme k).FullSubcategory) (a : W.H0 X) :
    (W.twCoord X 0 0 (W.h0TwEquiv X a) : W.H X) = a := by
  simp [h0TwEquiv, h0GradeEquiv]

/-- **The pairing `H^0(X) × H^{2d}(X)(d) → F`**, `(a, b) ↦ ∫_X a ∪ b`, for `X` nonempty and
equidimensional of dimension `d`. -/
def h0Pairing (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) :
    W.H0 X →ₗ[F] W.Tw X (2 * d) d →ₗ[F] F :=
  (W.pairingTw X d hX 0 (2 * d) (by ring) 0 d (by ring)).compl₁₂ (W.h0TwEquiv X).toLinearMap
    (LinearEquiv.refl F (W.Tw X (2 * d) d)).toLinearMap

/-- Axiom (A)(b) makes the pairing of `H^0(X)` with `H^{2d}(X)(d)` perfect. -/
theorem h0Pairing_isPerfPair (hA : W.PerfectPairing)
    (X : (SmoothProjectiveScheme k).FullSubcategory) (d : ℕ)
    (hX : IsNonemptyEquidimensional X d) : (W.h0Pairing X d hX).IsPerfPair := by
  have := hA.pairingTw X d hX 0 (2 * d) (by ring) 0 d (by ring)
  unfold h0Pairing
  infer_instance

/-- **The pairing of `a ∈ H^0(Y)` with the class of a closed subscheme of dimension zero.** Let
`i : Z ⟶ Y` be a closed immersion of a nonempty smooth projective scheme of dimension zero into
a nonempty one equidimensional of dimension `d`. If `∫_Z` is the trace map of the `F`-algebra
`H^0(Z)` (Stacks 0FHQ (4)), then `∫_Y a ∪ γ([Z]) = Tr_{H^0(Z)/F}(i^*a)`: by Stacks 0FHG,
`γ([Z]) = i_*1`, and `∫_Y a ∪ i_*1 = ∫_Z i^*a`. -/
theorem h0Pairing_cycleClass_closedSubschemeClass (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {Y Z : (SmoothProjectiveScheme k).FullSubcategory}
        (i : Z ⟶ Y)
    [IsClosedImmersion i.hom.left] {d : ℕ} (hY : IsNonemptyEquidimensional Y d)
    (hZ : IsNonemptyEquidimensional Z 0)
    (htr : ∀ c : W.H0 Z, W.trace Z 0 hZ (W.h0TwEquiv Z c) = Algebra.trace F (W.H0 Z) c)
    (a : W.H0 Y) :
    W.h0Pairing Y d hY a (W.cycleClass Y d (closedSubschemeClass Y.obj.hom i.hom.left d)) =
      Algebra.trace F (W.H0 Z) (H0.pullHom W i a) := by
  rw [W.cycleClass_closedSubschemeClass_eq_pushforward_one hA hB hC i hZ hY d (by simp)]
  simp only [h0Pairing, LinearMap.compl₁₂_apply, LinearEquiv.coe_coe, LinearEquiv.refl_apply]
  rw [← pushforward_trace' hA.perfectPairing i hZ hY 0 0 (2 * d) d (by ring) (by ring) 0 0
    (by ring) (by ring) (by ring) (by ring) (W.h0TwEquiv Y a) (W.unitTw Z 0 0 rfl),
    pairingTw_apply, ← htr]
  congr 1
  refine (W.twCoord Z (2 * ((0 : ℕ) : ℤ)) ((0 : ℕ) : ℤ)).injective (Subtype.ext ?_)
  rw [twCoord_cupTw, coe_cup, W.coe_twCoord_unitTw Z _ _ rfl, mul_one, twCoord_pullTw,
    coe_pullDeg, twCoord_h0TwEquiv]
  exact (W.twCoord_h0TwEquiv Z (H0.pullHom W i a)).symm


/-! ### The equidimensional case -/

/-- `H^0(X)` is finite dimensional by axiom (A)(a). -/
theorem finiteDimensional_H0 (hA : W.PoincareDuality)
    {X : (SmoothProjectiveScheme k).FullSubcategory} {d : ℕ}
    (hX : IsNonemptyEquidimensional X d) : FiniteDimensional F (W.H0 X) := by
  have := hA.finiteDimensionality X d hX 0
  exact LinearEquiv.finiteDimensional (W.h0GradeEquiv X).symm

/-- Pullback along a section is split by the pullback along the retraction. -/
theorem pullHom_comp_pullHom_of_comp_eq_id {S Y : (SmoothProjectiveScheme k).FullSubcategory}
    (x : S ⟶ Y)
    (q : Y ⟶ S) (hx : x ≫ q = 𝟙 S) :
    (H0.pullHom W x).comp (H0.pullHom W q) = AlgHom.id F (W.H0 S) := by
  ext c
  change W.pull x (W.pull q c) = c
  rw [← AlgHom.comp_apply, ← W.pull_comp, hx, W.pull_id, AlgHom.id_apply]

end WeilData

/-! ### Zero cycles over a finite separable extension -/

section Extension

variable {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k']

/-- Transport of the class of a closed subscheme along an equality of structure morphisms. -/
theorem chowGroupCongr_mk_cycleAssociatedToClosedSubscheme {C : ChowSituation.{u}}
    {T Z : Scheme.{u}} {s s' : T ⟶ C.S} [LocallyOfFiniteType s] [LocallyOfFiniteType s']
    (h : s = s') (i : Z ⟶ T) [IsClosedImmersion i] (n : ℤ) :
    chowGroupCongr C h n (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C s i n)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme C s' i n) := by
  subst h
  rfl

variable (Y : (SmoothProjectiveScheme k).FullSubcategory)
    (q : Y.obj.left ⟶ (fieldChowSituation k').S)
  [LocallyOfFiniteType q] (hqY : q ≫ fieldExtensionSpecMap k k' = Y.obj.hom)

/-- **A zero cycle class over `k'` as a class of codimension `i` over `k`**: the identification of
`CH_0(Y)` over `k'` with `CH_0(Y)` over `k` (`Stacks.Chow.chowGroupFiniteExtensionEquiv`)
followed by `CH_0(Y) ⟶ CH^i(Y)`. -/
def zeroCycleToCodimensionOfExtension (i : ℤ) :
    chowGroup (fieldChowSituation k') q 0 →+ codimensionChowGroup k Y.obj.hom i :=
  (zeroCycleToCodimension Y.obj.hom i).comp
    ((chowGroupCongr (fieldChowSituation k) hqY 0).toAddMonoidHom.comp
      (chowGroupFiniteExtensionEquiv k k' q 0).toAddMonoidHom)

/-- The image of the class over `k'` of a closed subscheme of dimension zero is its class
`[Z] ∈ CH^i(Y)`. -/
theorem zeroCycleToCodimensionOfExtension_mk {Z : Scheme.{u}} (j : Z ⟶ Y.obj.left)
    [IsClosedImmersion j]
    (hZ : ∀ z : Z, relativeDimension (fieldChowSituation k).dimensionFunction (j ≫ Y.obj.hom) z = 0)
    (i : ℤ) :
    zeroCycleToCodimensionOfExtension Y q hqY i
        (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k') q j 0)) =
      closedSubschemeClass Y.obj.hom j i := by
  simp only [zeroCycleToCodimensionOfExtension, AddMonoidHom.comp_apply,
    AddEquiv.coe_toAddMonoidHom]
  rw [show chowGroupFiniteExtensionEquiv k k' q 0
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k') q j 0)) =
      QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k)
        (q ≫ fieldExtensionSpecMap k k') j 0) from
    congrArg (QuotientAddGroup.mk' _)
      (cycleGroupEquivOfRelativeDimension_cycleAssociatedToClosedSubscheme _ _
        (sameRelativeDimension_fieldExtension k k' q) j 0),
    chowGroupCongr_mk_cycleAssociatedToClosedSubscheme]
  exact zeroCycleToCodimension_mk_cycleAssociatedToClosedSubscheme Y.obj.hom j hZ i

/-- A morphism `Spec k' ⟶ Spec k` equal to the structure morphism has relative dimension zero. -/
private theorem relativeDimension_eq_zero_of_eq_specStructure
    {s : (fieldChowSituation k').S ⟶ (fieldChowSituation k).S}
    (hs : s = SmoothProjectiveScheme.specStructure k k') (t : (fieldChowSituation k').S) :
    relativeDimension (fieldChowSituation k).dimensionFunction s t = 0 := by
  rw [hs, show SmoothProjectiveScheme.specStructure k k' = 𝟙 _ ≫ fieldExtensionSpecMap k k' from
      (Category.id_comp _).symm, relativeDimension_comp_fieldExtension k k' (𝟙 _) t,
    relativeDimension_id]
  rfl

omit [FiniteDimensional k k'] [LocallyOfFiniteType q] in
include hqY in
/-- **Separable residue fields over `k'` are separable over `k`**, `k'/k` being separable: the
residue field is a tower `k ⊆ k' ⊆ κ(z)`. -/
theorem hasSeparableResidueField_of_extension [Algebra.IsSeparable k k'] {z : Y.obj.left}
    (hz : HasSeparableResidueField k' q z) : HasSeparableResidueField k Y.obj.hom z := by
  unfold HasSeparableResidueField at hz ⊢
  let : Algebra k' (Y.obj.left.residueField z) :=
    ((Scheme.ΓSpecIso (.of k')).inv ≫ q.appTop ≫ Y.obj.left.Γevaluation z).hom.toAlgebra
  let : Algebra k (Y.obj.left.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ Y.obj.hom.appTop ≫ Y.obj.left.Γevaluation z).hom.toAlgebra
  have : IsScalarTower k k' (Y.obj.left.residueField z) := by
    refine IsScalarTower.of_algebraMap_eq fun a ↦ ?_
    change ((Scheme.ΓSpecIso (.of k)).inv ≫ Y.obj.hom.appTop ≫ Y.obj.left.Γevaluation z) a =
      ((Scheme.ΓSpecIso (.of k')).inv ≫ q.appTop ≫ Y.obj.left.Γevaluation z)
        (CommRingCat.ofHom (algebraMap k k') a)
    have h1 : (Scheme.ΓSpecIso (.of k)).inv ≫ (fieldExtensionSpecMap k k').appTop =
        CommRingCat.ofHom (algebraMap k k') ≫ (Scheme.ΓSpecIso (.of k')).inv :=
      (Scheme.ΓSpecIso_inv_naturality _).symm
    rw [← hqY, Scheme.Hom.comp_appTop]
    simp only [← Category.assoc]
    rw [h1]
    rfl
  exact Algebra.IsSeparable.trans k k' (Y.obj.left.residueField z)

end Extension

/-! ### Points of a scheme over `k`, and their restrictions to open subschemes -/

section PointCycles

variable {T : Scheme.{u}} (sT : T ⟶ (fieldChowSituation k).S) {L : Type u} [Field L]

/-- **The cycle of a point `Spec L ⟶ T` of relative dimension zero** is the prime cycle of its
image with coefficient one, in dimension zero. -/
theorem cycleAssociatedToClosedSubscheme_specField_val [LocallyOfFiniteType sT]
    (i : Spec (.of L) ⟶ T) [IsClosedImmersion i]
    (h : relativeDimension (fieldChowSituation k).dimensionFunction sT
      (i (genericPoint (Spec (.of L)))) = 0) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sT i 0).1 =
      @Function.locallyFinsuppWithin.single T _ ℤ (Classical.decEq T) _
        (i (genericPoint (Spec (.of L)))) 1 := by
  classical
  have hmem : genericPoint (Spec (.of L)) ∈ genericPoints (Spec (.of L)) :=
    genericPoint_mem_genericPoints _
  ext y
  by_cases hy : y = i (genericPoint (Spec (.of L)))
  · subst hy
    rw [show i (genericPoint (Spec (.of L))) = i (⟨_, hmem⟩ : genericPoints _).1 from rfl,
      cycleAssociatedToClosedSubscheme_apply _ sT i 0 ⟨_, hmem⟩ h,
      componentMultiplicity_eq_one i hmem]
    simp
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero, Function.locallyFinsuppWithin.single_apply,
      ite_eq_right hy]
    · rintro ⟨ξ, hξ, -⟩
      have : Subsingleton (Spec (.of L)) := inferInstanceAs (Subsingleton (PrimeSpectrum L))
      exact hy (hξ ▸ congrArg i.base (Subsingleton.elim _ _))

variable [LocallyOfFiniteType sT] {U : Scheme.{u}} (j : U ⟶ T) [IsOpenImmersion j]

/-- **Restricting the cycle of a point to an open subscheme containing it.** -/
theorem cycleGroupRestrict_cycleAssociatedToClosedSubscheme_specField (n : ℤ)
    (i : Spec (.of L) ⟶ U) [IsClosedImmersion i] [IsClosedImmersion (i ≫ j)]
    (h : ∀ z, relativeDimension (fieldChowSituation k).dimensionFunction ((i ≫ j) ≫ sT) z = 0) :
    cycleGroupRestrict (fieldChowSituation k) sT (j ≫ sT) j rfl n
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sT (i ≫ j) n) =
      cycleAssociatedToClosedSubscheme (fieldChowSituation k) (j ≫ sT) i n := by
  classical
  have h' : ∀ z, relativeDimension (fieldChowSituation k).dimensionFunction (i ≫ (j ≫ sT)) z = 0 :=
    fun z ↦ by rw [← Category.assoc]; exact h z
  by_cases hn : n = 0
  · subst hn
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun u ↦ ?_)
    have h0 := h (genericPoint (Spec (.of L)))
    rw [relativeDimension_comp_closedImmersion] at h0
    have h0' := h' (genericPoint (Spec (.of L)))
    rw [relativeDimension_comp_closedImmersion] at h0'
    rw [cycleGroupRestrict_apply, cycleAssociatedToClosedSubscheme_specField_val sT (i ≫ j) h0,
      cycleAssociatedToClosedSubscheme_specField_val (j ≫ sT) i h0']
    simp only [Function.locallyFinsuppWithin.single_apply]
    exact if_congr ⟨fun e ↦ j.isOpenEmbedding.injective e, fun e ↦ e ▸ rfl⟩ rfl rfl
  · rw [cycleAssociatedToClosedSubscheme_eq_zero_of_ne sT (i ≫ j) h hn,
      cycleAssociatedToClosedSubscheme_eq_zero_of_ne (j ≫ sT) i h' hn, map_zero]

/-- **Restricting the cycle of a point to an open subscheme missing it** gives zero. -/
theorem cycleGroupRestrict_cycleAssociatedToClosedSubscheme_specField_eq_zero (n : ℤ)
    (i : Spec (.of L) ⟶ T) [IsClosedImmersion i]
    (h : ∀ z, relativeDimension (fieldChowSituation k).dimensionFunction (i ≫ sT) z = 0)
    (hU : i (genericPoint (Spec (.of L))) ∉ Set.range j) :
    cycleGroupRestrict (fieldChowSituation k) sT (j ≫ sT) j rfl n
        (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sT i n) = 0 := by
  classical
  by_cases hn : n = 0
  · subst hn
    refine Subtype.ext (Function.locallyFinsuppWithin.ext fun u ↦ ?_)
    have h0 := h (genericPoint (Spec (.of L)))
    rw [relativeDimension_comp_closedImmersion] at h0
    rw [cycleGroupRestrict_apply, cycleAssociatedToClosedSubscheme_specField_val sT i h0]
    simp only [Function.locallyFinsuppWithin.single_apply]
    rw [ite_eq_right fun e ↦ hU ⟨u, e⟩]
    rfl
  · rw [cycleAssociatedToClosedSubscheme_eq_zero_of_ne sT i h hn, map_zero]

omit [LocallyOfFiniteType sT] in
/-- Restriction of the class of a cycle is the class of the restricted cycle. -/
theorem chowGroupRestrict_mk_eq [LocallyOfFiniteType sT] {sU : U ⟶ (fieldChowSituation k).S}
    [LocallyOfFiniteType sU] (hj : j ≫ sT = sU) (n : ℤ)
    (c : CycleGroup (fieldChowSituation k) sT n) :
    chowGroupRestrict (fieldChowSituation k) sT sU j hj n (QuotientAddGroup.mk c) =
      QuotientAddGroup.mk (cycleGroupRestrict (fieldChowSituation k) sT sU j hj n c) :=
  rfl

end PointCycles

section CodimensionPoints

variable {X : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S) [Smooth sX] {L : Type u} [Field L]

/-- **The class of a point in the codimension of another part vanishes.** If the point
`x : Spec L ⟶ X`, of relative dimension zero, lies in the part `X_d` of `X` of dimension `d`,
then `[x] = 0` in `CH^i(X)` for `i ≠ d`. -/
theorem closedSubschemeClass_specField_eq_zero (x : Spec (.of L) ⟶ X) [IsClosedImmersion x]
    (h : ∀ z, relativeDimension (fieldChowSituation k).dimensionFunction (x ≫ sX) z = 0)
    {d : ℕ} (hd : x (genericPoint (Spec (.of L))) ∈ dimPart sX d) {i : ℤ} (hi : i ≠ d) :
    closedSubschemeClass sX x i = 0 := by
  funext e
  rw [closedSubschemeClass_apply, chowGroupRestrict_mk_eq]
  by_cases he : x (genericPoint (Spec (.of L))) ∈ dimPart sX e
  · have hed : e = d := by
      by_contra hne
      have hmem : x (genericPoint (Spec (.of L))) ∈ dimPart sX e ⊓ dimPart sX d := ⟨he, hd⟩
      rw [((isClopenDecomposition_dimPart sX).disjoint e d hne).eq_bot] at hmem
      exact hmem
    subst hed
    rw [cycleAssociatedToClosedSubscheme_eq_zero_of_ne sX x h (by omega), map_zero]
    rfl
  · rw [cycleGroupRestrict_cycleAssociatedToClosedSubscheme_specField_eq_zero sX
      (dimPart sX e).ι _ x h (by rwa [Scheme.Opens.range_ι])]
    rfl

variable {U : Scheme.{u}} (sU : U ⟶ (fieldChowSituation k).S) [Smooth sU] (j : U ⟶ X)
  [IsOpenImmersion j] (hj : j ≫ sX = sU)

/-- The part of dimension `e` of `j^![Z]`, as the restriction to `U_e` of the restriction to `U`
of the cycle of `Z`. -/
private theorem codimensionGysin_closedSubschemeClass_apply_restrict {Z : Scheme.{u}} (x : Z ⟶ X)
    [IsClosedImmersion x] (i : ℤ) (e : ℕ) :
    codimensionGysin sU sX hj i (closedSubschemeClass sX x i) e =
      chowGroupRestrict (fieldChowSituation k) sU (partBase sU e) (dimPart sU e).ι rfl
        ((e : ℤ) - i) (chowGroupRestrict (fieldChowSituation k) sX sU j hj ((e : ℤ) - i)
          (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k) sX x
            ((e : ℤ) - i)))) := by
  subst hj
  rw [codimensionGysin_of_isOpenImmersion, closedSubschemeClass_apply, chowGroupRestrict_comp,
    chowGroupRestrict_comp]
  exact DFunLike.congr_fun (chowGroupRestrict_congr _ _ _ _ _ _ _ (dimPartMap_ι sX _ rfl e) _) _

include hj in
/-- **The Gysin map of an open immersion on the class of a point it contains**: for
`y : Spec L ⟶ U` of relative dimension zero, `j^![y ≫ j] = [y]` in `CH^i(U)`. -/
theorem codimensionGysin_closedSubschemeClass_specField (y : Spec (.of L) ⟶ U)
    [IsClosedImmersion y] [IsClosedImmersion (y ≫ j)]
    (h : ∀ z, relativeDimension (fieldChowSituation k).dimensionFunction ((y ≫ j) ≫ sX) z = 0)
    (i : ℤ) :
    codimensionGysin sU sX hj i (closedSubschemeClass sX (y ≫ j) i) =
      closedSubschemeClass sU y i := by
  subst hj
  funext e
  rw [codimensionGysin_closedSubschemeClass_apply_restrict, closedSubschemeClass_apply,
    chowGroupRestrict_mk_eq,
    cycleGroupRestrict_cycleAssociatedToClosedSubscheme_specField sX j _ y h]

include hj in
/-- **The Gysin map of an open immersion kills the class of a point it misses.** -/
theorem codimensionGysin_closedSubschemeClass_specField_eq_zero (x : Spec (.of L) ⟶ X)
    [IsClosedImmersion x]
    (h : ∀ z, relativeDimension (fieldChowSituation k).dimensionFunction (x ≫ sX) z = 0)
    (hU : x (genericPoint (Spec (.of L))) ∉ Set.range j) (i : ℤ) :
    codimensionGysin sU sX hj i (closedSubschemeClass sX x i) = 0 := by
  subst hj
  funext e
  rw [codimensionGysin_closedSubschemeClass_apply_restrict, chowGroupRestrict_mk_eq,
    cycleGroupRestrict_cycleAssociatedToClosedSubscheme_specField_eq_zero sX j _ x h hU]
  rfl

end CodimensionPoints

/-! ### The equidimensional case of Stacks 0FHU -/

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)
variable {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [Algebra.IsSeparable k k']

/-- **Stacks 0FHU for `Y` equidimensional**, granted Stacks 0FHQ (2) and (4) as the hypotheses
`h0fin`, `h0sep`, `h0tr`: if `[y] - [y']` is divisible by `n > 1` in `CH_0(Y)` for two
`k'`-rational points of `Y`, then `γ([y]) = γ([y'])`. This is the source's argument: by Stacks
0FH5 every class pairs with `H^0(Y)` as an integral combination of separable traces, by Stacks
0FHG and Stacks 0FHQ (4) the class of a rational point pairs as the trace of the pullback to
`H^0(Spec k')`, and Stacks 0FHT with Poincaré duality concludes
(`Stacks.WeilCohomology.rationalPointChowClass_sub_ne_zsmul`). -/
theorem cycleClass_eq_of_sub_eq_zsmul_of_equidimensional [CharZero F]
    (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    (h0fin : ∀ Z : (SmoothProjectiveScheme k).FullSubcategory, IsNonemptyEquidimensional Z 0 →
      FiniteDimensional F (W.H0 Z))
    (h0sep : ∀ Z : (SmoothProjectiveScheme k).FullSubcategory, IsNonemptyEquidimensional Z 0 →
      Algebra.IsSeparable F (W.H0 Z))
    (h0tr : ∀ (Z : (SmoothProjectiveScheme k).FullSubcategory) (hZ : IsNonemptyEquidimensional Z 0)
        (c : W.H0 Z),
      W.trace Z 0 hZ (W.h0TwEquiv Z c) = Algebra.trace F (W.H0 Z) c)
    (Y : (SmoothProjectiveScheme k).FullSubcategory) (q : Y.obj.left ⟶ (fieldChowSituation k').S)
        [Smooth q]
    (hq : IsProjectiveMorphism q) (hqY : q ≫ fieldExtensionSpecMap k k' = Y.obj.hom) {d : ℕ}
    (hY : IsNonemptyEquidimensional Y d) (y y' : (fieldChowSituation k').S ⟶ Y.obj.left)
    (hy : y ≫ q = 𝟙 _) (hy' : y' ≫ q = 𝟙 _) (n : ℤ) (hn : 1 < n)
    (c : chowGroup (fieldChowSituation k') q 0)
    (hdiv : rationalPointChowClass k' q y hy - rationalPointChowClass k' q y' hy' = n • c) :
    haveI := isClosedImmersion_of_comp_eq_id q y hy
    haveI := isClosedImmersion_of_comp_eq_id q y' hy'
    W.cycleClass Y d (closedSubschemeClass Y.obj.hom y d) =
      W.cycleClass Y d (closedSubschemeClass Y.obj.hom y' d) := by
  have := isClosedImmersion_of_comp_eq_id q y hy
  have := isClosedImmersion_of_comp_eq_id q y' hy'
  have hpt : ∀ x : (fieldChowSituation k').S ⟶ Y.obj.left, x ≫ q = 𝟙 _ →
      x ≫ Y.obj.hom = SmoothProjectiveScheme.specStructure k k' := fun x hx ↦ by
    rw [← hqY, ← Category.assoc, hx, Category.id_comp]
  let qH : Y ⟶ specField (k := k) k' := ObjectProperty.homMk (Over.homMk q hqY)
  have hsec : ∀ (x : (fieldChowSituation k').S ⟶ Y.obj.left) (hx : x ≫ q = 𝟙 _),
      specFieldHom x (hpt x hx) ≫ qH = 𝟙 _ := fun x hx ↦
    SmoothProjectiveScheme.hom_ext_left (by change x ≫ q = 𝟙 _; exact hx)
  have hZ := isNonemptyEquidimensional_specField (k := k) k'
  have := h0fin _ hZ
  have := h0sep _ hZ
  have := W.finiteDimensional_H0 hA hY
  have := W.h0Pairing_isPerfPair hA.perfectPairing Y d hY
  let cl : chowGroup (fieldChowSituation k') q 0 →+ W.Tw Y (2 * d) d :=
    (W.cycleClass Y d).comp (zeroCycleToCodimensionOfExtension Y q hqY d)
  -- the class of a rational point
  have hcl : ∀ (x : (fieldChowSituation k').S ⟶ Y.obj.left) (hx : x ≫ q = 𝟙 _),
      have := isClosedImmersion_of_comp_eq_id q x hx
      cl (rationalPointChowClass k' q x hx) =
        W.cycleClass Y d (closedSubschemeClass Y.obj.hom x d) := fun x hx ↦ by
    have := isClosedImmersion_of_comp_eq_id q x hx
    change W.cycleClass Y d (zeroCycleToCodimensionOfExtension Y q hqY d
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k') q x 0))) = _
    rw [zeroCycleToCodimensionOfExtension_mk Y q hqY x
      (relativeDimension_eq_zero_of_eq_specStructure (hpt x hx))]
  -- its pairing with `H^0(Y)` is a trace
  have htr : ∀ (x : (fieldChowSituation k').S ⟶ Y.obj.left) (hx : x ≫ q = 𝟙 _) (a : W.H0 Y),
      W.h0Pairing Y d hY a (cl (rationalPointChowClass k' q x hx)) =
        Algebra.trace F (W.H0 (specField (k := k) k'))
          (H0.pullHom W (specFieldHom x (hpt x hx)) a) :=
    fun x hx a ↦ by
    have : IsClosedImmersion (specFieldHom x (hpt x hx)).hom.left :=
      isClosedImmersion_of_comp_eq_id q x hx
    rw [hcl x hx]
    exact W.h0Pairing_cycleClass_closedSubschemeClass hA hB hC (specFieldHom x (hpt x hx)) hY hZ
      (h0tr _ hZ) a
  -- every class pairs with `H^0(Y)` as a combination of separable traces (Stacks 0FH5)
  have hsep : ∀ α : chowGroup (fieldChowSituation k') q 0,
      IsSeparableTraceCombination.{w, w, w} F (W.H0 Y) ((W.h0Pairing Y d hY).flip (cl α)) := by
    let S : AddSubgroup (chowGroup (fieldChowSituation k') q 0) :=
      { carrier := {α | IsSeparableTraceCombination.{w, w, w} F (W.H0 Y)
          ((W.h0Pairing Y d hY).flip (cl α))}
        zero_mem' := by
          change IsSeparableTraceCombination F (W.H0 Y) ((W.h0Pairing Y d hY).flip (cl 0))
          rw [map_zero, map_zero]
          exact IsSeparableTraceCombination.zero
        add_mem' := fun {a b} ha hb ↦ by
          change IsSeparableTraceCombination F (W.H0 Y) ((W.h0Pairing Y d hY).flip (cl (a + b)))
          rw [map_add, map_add]
          exact ha.add hb
        neg_mem' := fun {a} ha ↦ by
          change IsSeparableTraceCombination F (W.H0 Y) ((W.h0Pairing Y d hY).flip (cl (-a)))
          rw [map_neg, map_neg]
          exact ha.neg }
    have hgen : AddSubgroup.closure (separablePointClasses k' q) ≤ S := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨z, hz, hzsep, rfl⟩
      have hzsep' := hasSeparableResidueField_of_extension Y q hqY hzsep
      have hzk : IsClosed ({z} : Set Y.obj.left) := hz
      let zH := closedPointHom hzk hzsep'
      have hZz := isNonemptyEquidimensional_closedPointObj hzk hzsep'
      have := h0fin _ hZz
      have := h0sep _ hZz
      change IsSeparableTraceCombination F (W.H0 Y) ((W.h0Pairing Y d hY).flip (cl
        (QuotientAddGroup.mk' _ (cycleAssociatedToClosedSubscheme (fieldChowSituation k') q
          (integralComponentAt z).subschemeι 0))))
      have := isIntegral_integralComponentAt z
      have : IsIntegral (closedPointObj hzk hzsep').obj.left :=
        inferInstanceAs (IsIntegral (Spec (.of (Y.obj.left.residueField z))))
      rw [show cycleAssociatedToClosedSubscheme (fieldChowSituation k') q
          (integralComponentAt z).subschemeι 0 =
          cycleAssociatedToClosedSubscheme (fieldChowSituation k') q zH.hom.left 0 from
        cycleAssociatedToClosedSubscheme_eq_of_genericPoint_eq _ q _ _ (by
          rw [show zH.hom.left (genericPoint (closedPointObj hzk hzsep').obj.left) = z from
            Scheme.fromSpecResidueField_apply (X := Y.obj.left) z _]
          exact genericPointOf_integralComponentAt z) 0]
      have hval : cl (QuotientAddGroup.mk' _ (cycleAssociatedToClosedSubscheme
          (fieldChowSituation k') q zH.hom.left 0)) =
          W.cycleClass Y d (closedSubschemeClass Y.obj.hom zH.hom.left d) :=
        congrArg (W.cycleClass Y d) (zeroCycleToCodimensionOfExtension_mk Y q hqY zH.hom.left
          (relativeDimension_closedPointHom hzk hzsep') d)
      rw [hval]
      convert IsSeparableTraceCombination.trace (F := F) (W.H0 (closedPointObj hzk hzsep'))
        (H0.pullHom W zH) using 1
      exact LinearMap.ext fun a ↦
        W.h0Pairing_cycleClass_closedSubschemeClass hA hB hC zH hY hZz (h0tr _ hZz) a
    exact fun α ↦ hgen (mem_closure_separablePointClasses_of_isProjectiveMorphism k' q hq α)
  -- Stacks 0FHT and Poincaré duality
  by_contra hne
  refine rationalPointChowClass_sub_ne_zsmul q y y' hy hy' F (W.H0 (specField (k := k) k'))
    (W.H0 Y) (W.Tw Y (2 * d) d) (W.h0Pairing Y d hY) cl
    (H0.pullHom W (specFieldHom y (hpt y hy))) (H0.pullHom W (specFieldHom y' (hpt y' hy')))
    (H0.pullHom W qH) (W.pullHom_comp_pullHom_of_comp_eq_id _ _ (hsec y hy))
    (W.pullHom_comp_pullHom_of_comp_eq_id _ _ (hsec y' hy')) (htr y hy) (htr y' hy') hsep ?_
    n hn c hdiv
  rwa [hcl y hy, hcl y' hy']

end WeilData

/-! ### A smooth projective scheme over `k'` as one over `k` -/

section OverExtension

variable {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [Algebra.IsSeparable k k'] {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k').S) [Smooth p]
  (hp : IsProjectiveMorphism p)

/-- **A smooth projective scheme over a finite separable extension `k'/k`, as a smooth projective
scheme over `k`**, through `Spec k' ⟶ Spec k`. -/
abbrev ofOverField : (SmoothProjectiveScheme k).FullSubcategory :=
  haveI := etale_of_isSeparable (k := k) k'
  SmoothProjectiveScheme.ofOver k p hp

omit [Smooth p] in
include hp in
/-- The restriction to an open and closed subscheme is again smooth and projective. -/
theorem isProjectiveMorphism_opensι_comp (U : X.Opens) [IsClosedImmersion U.ι] :
    IsProjectiveMorphism (U.ι ≫ p) := by
  obtain ⟨n, i, hi, h⟩ := hp
  exact ⟨n, U.ι ≫ i, inferInstance, by rw [Category.assoc, h]⟩

omit [Algebra.IsSeparable k k'] in
/-- The points of `Spec k'` have relative dimension zero over `k`. -/
theorem relativeDimension_specStructure (z : Spec (.of k')) :
    relativeDimension (fieldChowSituation k).dimensionFunction
      (SmoothProjectiveScheme.specStructure k k') z = 0 := by
  exact relativeDimension_eq_zero_of_eq_specStructure rfl z

/-- A `k'`-rational point has relative dimension zero over `k`. -/
theorem relativeDimension_rationalPoint (x : (fieldChowSituation k').S ⟶ X) (hx : x ≫ p = 𝟙 _)
    (z : Spec (.of k')) :
    relativeDimension (fieldChowSituation k).dimensionFunction
      (x ≫ (ofOverField p hp).obj.hom) z = 0 := by
  refine relativeDimension_eq_zero_of_eq_specStructure ?_ z
  change x ≫ p ≫ _ = _
  rw [← Category.assoc, hx, Category.id_comp]

omit [Smooth p] [Algebra.IsSeparable k k'] in
/-- A `k'`-rational point of `X`, with `X` viewed over `k` through `s`, has relative dimension
zero over `k`. -/
theorem relativeDimension_comp_eq_zero_of_comp_eq_id {s : X ⟶ (fieldChowSituation k).S}
    (hps : p ≫ fieldExtensionSpecMap k k' = s) (z : (fieldChowSituation k').S ⟶ X)
    (hz : z ≫ p = 𝟙 _) (t : Spec (.of k')) :
    relativeDimension (fieldChowSituation k).dimensionFunction (z ≫ s) t = 0 := by
  refine relativeDimension_eq_zero_of_eq_specStructure ?_ t
  rw [← hps, ← Category.assoc, hz, Category.id_comp]

/-- **The class `[x] ∈ CH^i(X)` of a `k'`-rational point** `x` of `X`, `X` viewed over `k`: the
class of the closed subscheme `x : Spec k' ⟶ X` (`Stacks.WeilCohomology.closedSubschemeClass`). -/
def rationalPointClass (x : (fieldChowSituation k').S ⟶ X) (hx : x ≫ p = 𝟙 _) (i : ℤ) :
    codimensionChowGroup k (ofOverField p hp).obj.hom i :=
  @closedSubschemeClass k _ (ofOverField p hp).obj.left (Spec (.of k'))
    (ofOverField p hp).obj.hom _ x (isClosedImmersion_of_comp_eq_id p x hx) i

/-- `[Z]` depends only on the closed immersion. -/
theorem closedSubschemeClass_congr {T Z : Scheme.{u}} (sT : T ⟶ (fieldChowSituation k).S)
    [Smooth sT] {i i' : Z ⟶ T} [IsClosedImmersion i] [IsClosedImmersion i'] (h : i = i')
    (c : ℤ) : closedSubschemeClass sT i c = closedSubschemeClass sT i' c := by
  subst h
  rfl

omit [Algebra k k'] [FiniteDimensional k k'] [Algebra.IsSeparable k k'] [Smooth p] in
/-- **Restricting the class of a rational point to an open subscheme containing it.** -/
theorem chowGroupRestrict_rationalPointChowClass [LocallyOfFiniteType p] (U : X.Opens)
    (x : (fieldChowSituation k').S ⟶ X) (hx : x ≫ p = 𝟙 _) (y : (fieldChowSituation k').S ⟶ U)
    (hyx : y ≫ U.ι = x) :
    chowGroupRestrict (fieldChowSituation k') p (U.ι ≫ p) U.ι rfl 0
        (rationalPointChowClass k' p x hx) =
      rationalPointChowClass k' (U.ι ≫ p) y (by rw [← Category.assoc, hyx, hx]) := by
  have := isClosedImmersion_of_comp_eq_id p x hx
  have : IsClosedImmersion y :=
    isClosedImmersion_of_comp_eq_id (U.ι ≫ p) y (by rw [← Category.assoc, hyx, hx])
  have : IsClosedImmersion (y ≫ U.ι) := by rw [hyx]; infer_instance
  change chowGroupRestrict (fieldChowSituation k') p (U.ι ≫ p) U.ι rfl 0
      (QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k') p x 0)) =
    QuotientAddGroup.mk (cycleAssociatedToClosedSubscheme (fieldChowSituation k') (U.ι ≫ p) y 0)
  rw [← cycleAssociatedToClosedSubscheme_congr (fieldChowSituation k') p (y ≫ U.ι) x hyx,
    chowGroupRestrict_mk_eq, cycleGroupRestrict_cycleAssociatedToClosedSubscheme_specField p U.ι 0
      y (fun z ↦ by rw [hyx, hx, relativeDimension_id]; rfl)]

end OverExtension

/-- A rational point whose locus lies in an open subscheme factors through it. -/
theorem range_subset_range_ι_of_rationalPointLocus_mem {k' : Type u} [Field k'] {X : Scheme.{u}}
    (U : X.Opens) (z : (fieldChowSituation k').S ⟶ X) (hz : rationalPointLocus z ∈ U) :
    Set.range z ⊆ Set.range U.ι := by
  rintro _ ⟨t, rfl⟩
  rw [Scheme.Opens.range_ι]
  have : Subsingleton (Spec (.of k')) := inferInstanceAs (Subsingleton (PrimeSpectrum k'))
  rwa [Subsingleton.elim t (genericPoint _)]

/-- An open and closed subscheme and its complement are complementary open subschemes. -/
theorem isCompl_opensRange_ι_compl {X : Scheme.{u}} {U : X.Opens} (hU : IsClopen (U : Set X)) :
    IsCompl U.ι.opensRange
      (Scheme.Opens.ι ⟨(U : Set X)ᶜ, hU.isClosed.isOpen_compl⟩).opensRange := by
  rw [Scheme.Opens.opensRange_ι, Scheme.Opens.opensRange_ι]
  refine ⟨disjoint_iff.mpr ?_, codisjoint_iff.mpr ?_⟩ <;> ext z <;> simp

namespace WeilData

variable {F : Type w} [Field F] (W : WeilData k F)
variable {k' : Type u} [Field k'] [Algebra k k'] [FiniteDimensional k k']
  [Algebra.IsSeparable k k']

/-- **Stacks 0FHJ, injectivity, in every degree and twist**: a class on a coproduct is determined
by its pullbacks to the two summands. -/
theorem eq_of_pullTw_eq_of_isColimit [CharZero F] (hA : W.PoincareDuality) (hB : W.Kunneth)
    (hC : W.CycleClassAxiom hA.perfectPairing) {A B : (SmoothProjectiveScheme k).FullSubcategory}
    {c : BinaryCofan A B} (hc : IsColimit c) (n m : ℤ) (a b : W.Tw c.pt n m)
    (h₁ : W.pullTw c.inl n m a = W.pullTw c.inl n m b)
    (h₂ : W.pullTw c.inr n m a = W.pullTw c.inr n m b) : a = b := by
  apply (W.twCoord c.pt n m).injective
  apply Subtype.ext
  apply (W.pullbackPair_bijective_of_isColimit hA hB hC hc).injective
  have e₁ := congrArg (fun t ↦ ((W.twCoord A n m t : W.grade A n) : W.H A)) h₁
  have e₂ := congrArg (fun t ↦ ((W.twCoord B n m t : W.grade B n) : W.H B)) h₂
  dsimp only at e₁ e₂
  rw [twCoord_pullTw, twCoord_pullTw, coe_pullDeg, coe_pullDeg] at e₁ e₂
  exact Prod.ext e₁ e₂

/-- The pullback of the class of a point along an open immersion through which it factors is the
class of the lifted point. -/
theorem pullTw_cycleClass_closedSubschemeClass_specField (hA : W.PoincareDuality)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (j : Y ⟶ X) [IsOpenImmersion j.hom.left] {L : Type u} [Field L]
    (z : Spec (.of L) ⟶ X.obj.left) [IsClosedImmersion z] (w : Spec (.of L) ⟶ Y.obj.left)
    [IsClosedImmersion w] (hwz : w ≫ j.hom.left = z)
    (h : ∀ t, relativeDimension (fieldChowSituation k).dimensionFunction (z ≫ X.obj.hom) t = 0)
    (i : ℤ) :
    W.pullTw j _ _ (W.cycleClass X i (closedSubschemeClass X.obj.hom z i)) =
      W.cycleClass Y i (closedSubschemeClass Y.obj.hom w i) := by
  have : IsClosedImmersion (w ≫ j.hom.left) := by
    rw [hwz]
    infer_instance
  rw [← hC.pullback j]
  congr 1
  rw [closedSubschemeClass_congr X.obj.hom hwz.symm i]
  exact codimensionGysin_closedSubschemeClass_specField X.obj.hom Y.obj.hom j.hom.left
    (Over.w j.hom) w (fun t ↦ by rw [hwz]; exact h t) i

/-- The pullback of the class of a point along an open immersion missing it vanishes. -/
theorem pullTw_cycleClass_closedSubschemeClass_specField_eq_zero (hA : W.PoincareDuality)
    (hC : W.CycleClassAxiom hA.perfectPairing) {X Y : (SmoothProjectiveScheme k).FullSubcategory}
    (j : Y ⟶ X) [IsOpenImmersion j.hom.left] {L : Type u} [Field L]
    (z : Spec (.of L) ⟶ X.obj.left) [IsClosedImmersion z]
    (h : ∀ t, relativeDimension (fieldChowSituation k).dimensionFunction (z ≫ X.obj.hom) t = 0)
    (hz : z (genericPoint (Spec (.of L))) ∉ Set.range j.hom.left) (i : ℤ) :
    W.pullTw j _ _ (W.cycleClass X i (closedSubschemeClass X.obj.hom z i)) = 0 := by
  rw [← hC.pullback j, codimensionGysin_closedSubschemeClass_specField_eq_zero X.obj.hom
    Y.obj.hom j.hom.left (Over.w j.hom) z h hz i, map_zero]

/-- **The classes of two points of one summand of a coproduct** agree once the classes of the
points lifted to that summand agree. -/
theorem cycleClass_closedSubschemeClass_eq_of_isColimit [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    {X Y Yc : (SmoothProjectiveScheme k).FullSubcategory} {j : Y ⟶ X} {jc : Yc ⟶ X}
    (hc : IsColimit (BinaryCofan.mk j jc)) [IsOpenImmersion j.hom.left]
    [IsOpenImmersion jc.hom.left] (hdisj : Disjoint (Set.range j.hom.left) (Set.range jc.hom.left))
    {L : Type u} [Field L] {w w' : Spec (.of L) ⟶ Y.obj.left} [IsClosedImmersion w]
    [IsClosedImmersion w'] {z z' : Spec (.of L) ⟶ X.obj.left} [IsClosedImmersion z]
    [IsClosedImmersion z'] (hwz : w ≫ j.hom.left = z) (hwz' : w' ≫ j.hom.left = z')
    (h : ∀ t, relativeDimension (fieldChowSituation k).dimensionFunction (z ≫ X.obj.hom) t = 0)
    (h' : ∀ t, relativeDimension (fieldChowSituation k).dimensionFunction (z' ≫ X.obj.hom) t = 0)
    (i : ℤ)
    (hw : W.cycleClass Y i (closedSubschemeClass Y.obj.hom w i) =
      W.cycleClass Y i (closedSubschemeClass Y.obj.hom w' i)) :
    W.cycleClass X i (closedSubschemeClass X.obj.hom z i) =
      W.cycleClass X i (closedSubschemeClass X.obj.hom z' i) := by
  refine W.eq_of_pullTw_eq_of_isColimit hA hB hC hc (2 * i) i _ _ ?_ ?_
  · change W.pullTw j _ _ _ = W.pullTw j _ _ _
    rw [W.pullTw_cycleClass_closedSubschemeClass_specField hA hC j z w hwz h,
      W.pullTw_cycleClass_closedSubschemeClass_specField hA hC j z' w' hwz' h']
    exact hw
  · change W.pullTw jc _ _ _ = W.pullTw jc _ _ _
    subst hwz hwz'
    rw [W.pullTw_cycleClass_closedSubschemeClass_specField_eq_zero hA hC jc _ h
        (Set.disjoint_left.mp hdisj ⟨w _, rfl⟩),
      W.pullTw_cycleClass_closedSubschemeClass_specField_eq_zero hA hC jc _ h'
        (Set.disjoint_left.mp hdisj ⟨w' _, rfl⟩)]

/-- **Stacks 0FHU, two points in one part**: if `x` and `x'` lie in the part `X'_d` of `X'` of
dimension `d` and `[x] - [x']` is divisible by `n > 1`, then `γ([x]) = γ([x'])` in
`H^{2d}(X')(d)`. -/
theorem cycleClass_rationalPoint_eq_of_mem_dimPart [CharZero F]
    (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    (h0fin : ∀ Z : (SmoothProjectiveScheme k).FullSubcategory, IsNonemptyEquidimensional Z 0 →
      FiniteDimensional F (W.H0 Z))
    (h0sep : ∀ Z : (SmoothProjectiveScheme k).FullSubcategory, IsNonemptyEquidimensional Z 0 →
      Algebra.IsSeparable F (W.H0 Z))
    (h0tr : ∀ (Z : (SmoothProjectiveScheme k).FullSubcategory) (hZ : IsNonemptyEquidimensional Z 0)
        (c : W.H0 Z),
      W.trace Z 0 hZ (W.h0TwEquiv Z c) = Algebra.trace F (W.H0 Z) c)
    (X' : (SmoothProjectiveScheme k).FullSubcategory) (p : X'.obj.left ⟶ (fieldChowSituation k').S)
        [Smooth p]
    (hp : IsProjectiveMorphism p) (hpX : p ≫ fieldExtensionSpecMap k k' = X'.obj.hom)
    (x x' : (fieldChowSituation k').S ⟶ X'.obj.left) (hx : x ≫ p = 𝟙 _) (hx' : x' ≫ p = 𝟙 _)
    {d : ℕ} (hd : rationalPointLocus x ∈ dimPart X'.obj.hom d)
    (hd' : rationalPointLocus x' ∈ dimPart X'.obj.hom d)
    (n : ℤ) (hn : 1 < n) (c : chowGroup (fieldChowSituation k') p 0)
    (hdiv : rationalPointChowClass k' p x hx - rationalPointChowClass k' p x' hx' = n • c) :
    haveI := isClosedImmersion_of_comp_eq_id p x hx
    haveI := isClosedImmersion_of_comp_eq_id p x' hx'
    W.cycleClass X' d (closedSubschemeClass X'.obj.hom x d) =
      W.cycleClass X' d (closedSubschemeClass X'.obj.hom x' d) := by
  have := isClosedImmersion_of_comp_eq_id p x hx
  have := isClosedImmersion_of_comp_eq_id p x' hx'
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have := etale_of_isSeparable (k := k) k'
  set sX := X'.obj.hom
  set U := dimPart sX d
  have : IsClosedImmersion U.ι := (isClopenDecomposition_dimPart sX).isClosedImmersion_ι d
  have : IsProper (U.ι ≫ p) := inferInstance
  have hUcl := (isClopenDecomposition_dimPart sX).isClopen d
  let V : X'.obj.left.Opens := ⟨(U : Set X'.obj.left)ᶜ, hUcl.isClosed.isOpen_compl⟩
  have : IsClosedImmersion V.ι := IsClosedImmersion.of_isPreimmersion V.ι
    (by rw [Scheme.Opens.range_ι]; exact hUcl.isOpen.isClosed_compl)
  have hsU : Smooth (U.ι ≫ p) := inferInstance
  have : Smooth (V.ι ≫ p) := inferInstance
  let Y := ofOverField (k := k) (U.ι ≫ p) (isProjectiveMorphism_opensι_comp p hp U)
  let Yc := ofOverField (k := k) (V.ι ≫ p) (isProjectiveMorphism_opensι_comp p hp V)
  have hjw : U.ι ≫ sX = Y.obj.hom := by
    rw [← hpX, ← Category.assoc]; rfl
  have hjcw : V.ι ≫ sX = Yc.obj.hom := by
    rw [← hpX, ← Category.assoc]; rfl
  let j : Y ⟶ X' := ObjectProperty.homMk (Over.homMk U.ι hjw)
  let jc : Yc ⟶ X' := ObjectProperty.homMk (Over.homMk V.ι hjcw)
  have hc : IsColimit (BinaryCofan.mk j jc) :=
    SmoothProjectiveScheme.isColimitOfIsColimitMapCofan
      (nonempty_isColimit_binaryCofanMk_of_isCompl U.ι V.ι (isCompl_opensRange_ι_compl hUcl)).some
  let y := IsOpenImmersion.lift U.ι x (range_subset_range_ι_of_rationalPointLocus_mem U x hd)
  let y' := IsOpenImmersion.lift U.ι x' (range_subset_range_ι_of_rationalPointLocus_mem U x' hd')
  have hyx : y ≫ U.ι = x := IsOpenImmersion.lift_fac _ _ _
  have hyx' : y' ≫ U.ι = x' := IsOpenImmersion.lift_fac _ _ _
  have hy : y ≫ (U.ι ≫ p) = 𝟙 _ := by rw [← Category.assoc, hyx, hx]
  have hy' : y' ≫ (U.ι ≫ p) = 𝟙 _ := by rw [← Category.assoc, hyx', hx']
  have : @IsClosedImmersion _ Y.obj.left y := isClosedImmersion_of_comp_eq_id (U.ι ≫ p) y hy
  have : @IsClosedImmersion _ Y.obj.left y' := isClosedImmersion_of_comp_eq_id (U.ι ≫ p) y' hy'
  have : IsOpenImmersion j.hom.left := inferInstanceAs (IsOpenImmersion U.ι)
  have : IsOpenImmersion jc.hom.left := inferInstanceAs (IsOpenImmersion V.ι)
  have hYd : IsNonemptyEquidimensional Y d := by
    refine ⟨⟨⟨rationalPointLocus x, hd⟩⟩, ?_⟩
    change RelativeDimension ((U.ι ≫ p) ≫ SmoothProjectiveScheme.specStructure k k') d
    simpa only [partBase, sX, ← hpX, Category.assoc] using relativeDimension_partBase sX d
  have hdivU := congrArg (chowGroupRestrict (fieldChowSituation k') p (U.ι ≫ p) U.ι rfl 0) hdiv
  rw [map_sub, map_zsmul, chowGroupRestrict_rationalPointChowClass p U x hx y hyx,
    chowGroupRestrict_rationalPointChowClass p U x' hx' y' hyx'] at hdivU
  have : Smooth (U.ι ≫ p : Y.obj.left ⟶ (fieldChowSituation k').S) := hsU
  have hdisj : Disjoint (Set.range U.ι) (Set.range V.ι) := by
    simpa [Scheme.Opens.range_ι, V] using disjoint_compl_right
  exact W.cycleClass_closedSubschemeClass_eq_of_isColimit hA hB hC hc hdisj hyx hyx'
    (relativeDimension_comp_eq_zero_of_comp_eq_id p hpX x hx)
    (relativeDimension_comp_eq_zero_of_comp_eq_id p hpX x' hx') d
    (W.cycleClass_eq_of_sub_eq_zsmul_of_equidimensional hA hB hC h0fin h0sep h0tr Y (U.ι ≫ p)
      (isProjectiveMorphism_opensι_comp p hp U) rfl hYd y y' hy hy' n hn _ hdivU)

/-- **Stacks 0FHU**, granted Stacks 0FHQ (2), (4) (`h0fin`, `h0sep`, `h0tr`), for a smooth
projective `k`-scheme `X'` with a structure `p : X' ⟶ Spec k'` over `k'`. -/
theorem rationalPointChowClass_sub_ne_zsmul_of_hypotheses [CharZero F]
    (hA : W.PoincareDuality) (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing)
    (h0fin : ∀ Z : (SmoothProjectiveScheme k).FullSubcategory, IsNonemptyEquidimensional Z 0 →
      FiniteDimensional F (W.H0 Z))
    (h0sep : ∀ Z : (SmoothProjectiveScheme k).FullSubcategory, IsNonemptyEquidimensional Z 0 →
      Algebra.IsSeparable F (W.H0 Z))
    (h0tr : ∀ (Z : (SmoothProjectiveScheme k).FullSubcategory) (hZ : IsNonemptyEquidimensional Z 0)
        (c : W.H0 Z),
      W.trace Z 0 hZ (W.h0TwEquiv Z c) = Algebra.trace F (W.H0 Z) c)
    (X' : (SmoothProjectiveScheme k).FullSubcategory) (p : X'.obj.left ⟶ (fieldChowSituation k').S)
        [Smooth p]
    (hp : IsProjectiveMorphism p) (hpX : p ≫ fieldExtensionSpecMap k k' = X'.obj.hom)
    (x x' : (fieldChowSituation k').S ⟶ X'.obj.left) (hx : x ≫ p = 𝟙 _) (hx' : x' ≫ p = 𝟙 _)
    (hne : haveI := isClosedImmersion_of_comp_eq_id p x hx
      haveI := isClosedImmersion_of_comp_eq_id p x' hx'
      (fun i : ℤ ↦ W.cycleClass X' i (closedSubschemeClass X'.obj.hom x i)) ≠
        fun i : ℤ ↦ W.cycleClass X' i (closedSubschemeClass X'.obj.hom x' i))
    (n : ℤ) (hn : 1 < n) (c : chowGroup (fieldChowSituation k') p 0) :
    rationalPointChowClass k' p x hx - rationalPointChowClass k' p x' hx' ≠ n • c := by
  intro hdiv
  have := isClosedImmersion_of_comp_eq_id p x hx
  have := isClosedImmersion_of_comp_eq_id p x' hx'
  have : IsProper p := isProper_of_isProjectiveMorphism p hp
  have := etale_of_isSeparable (k := k) k'
  set sX := X'.obj.hom
  obtain ⟨d, hd⟩ := (isClopenDecomposition_dimPart sX).exists_mem (rationalPointLocus x)
  set U := dimPart sX d
  have : IsClosedImmersion U.ι := (isClopenDecomposition_dimPart sX).isClosedImmersion_ι d
  have : IsProper (U.ι ≫ p) := inferInstance
  by_cases hx'U : rationalPointLocus x' ∈ U
  swap
  · exact rationalPointChowClass_sub_ne_zsmul_of_mem_of_notMem p U x x' hx hx' hd hx'U n hn c
      hdiv
  refine hne (funext fun i ↦ ?_)
  by_cases hi : i = d
  · subst hi
    exact W.cycleClass_rationalPoint_eq_of_mem_dimPart hA hB hC h0fin h0sep h0tr X' p hp hpX x x'
      hx hx' hd hx'U n hn c hdiv
  · change W.cycleClass X' i (closedSubschemeClass sX x i) =
      W.cycleClass X' i (closedSubschemeClass sX x' i)
    rw [closedSubschemeClass_specField_eq_zero sX x
        (relativeDimension_comp_eq_zero_of_comp_eq_id p hpX x hx) hd hi,
      closedSubschemeClass_specField_eq_zero sX x'
        (relativeDimension_comp_eq_zero_of_comp_eq_id p hpX x' hx') hx'U hi]

/-- **Stacks Project, Tag 0FHU.** Assume given (D0), (D1), (D2) and (D3) satisfying (A), (B) and
(C). Let `k'/k` be a finite separable extension, let `X` be a smooth projective scheme over `k'`
and let `x, x' ∈ X` be `k'`-rational points. If `γ(x) ≠ γ(x')`, then `[x] - [x']` is not
divisible by any integer `n > 1` in `CH_0(X)`.

Here `X` is a scheme with a smooth projective structure morphism `p : X ⟶ Spec k'`, and it is a
smooth projective scheme over `k` through `Spec k' ⟶ Spec k` (`ofOverField p hp`), which is how
the data (D0)–(D3) over `k` apply to it. The points are sections `x, x'` of `p`;
`[x], [x'] ∈ CH_0(X)` are their classes in the Chow group of `X` over `k'`
(`rationalPointChowClass`), and the divisibility is in that group. `γ(x)` is the family of the
cohomology classes `γ([x]) ∈ H^{2i}(X)(i)` of the class `[x] ∈ CH^i(X)` of the closed subscheme
`x` in every codimension `i` (`rationalPointClass`): on the part of `X` of dimension `d`
containing `x` this is `γ([x]) ∈ H^{2d}(X)(d)`, the other entries vanishing.

The proof is the source's. If `x` and `x'` lie in different parts of `X` of constant dimension,
the degree on the part containing `x` separates them. Otherwise, on that part `X_d`, Stacks 0FH5
writes the class of every zero cycle as an integral combination of classes of closed points with
separable residue field, Stacks 0FHG and Stacks 0FHQ identify `a ↦ ∫ a ∪ γ([y])` on `H^0(X_d)`
with `Tr_{H^0(y)/F} ∘ i_y^*`, Poincaré duality (A)(b) turns the divisibility into the trace
relation of Stacks 0FHT, which forces `i_x^* = i_{x'}^*`, whence `γ([x]) = γ([x'])` on `X_d`; and
by (C)(a), the Gysin map of an open immersion being restriction, and Stacks 0FHJ for
`X = X_d ⨿ (X ∖ X_d)`, `γ(x) = γ(x')` on `X`. -/
@[stacks 0FHU "for X smooth projective over a finite separable k'/k, viewed over k, with the \
  actual CH_0(X) over k', the data (D0)-(D3) and axioms (A), (B), (C) over the actual category of \
  smooth projective k-schemes; γ(x) is the family of the classes γ([x]) in every codimension"]
theorem rationalPointChowClass_sub_ne_zsmul [CharZero F] (hA : W.PoincareDuality)
    (hB : W.Kunneth) (hC : W.CycleClassAxiom hA.perfectPairing) {X : Scheme.{u}}
    (p : X ⟶ (fieldChowSituation k').S) [Smooth p] (hp : IsProjectiveMorphism p)
    (x x' : (fieldChowSituation k').S ⟶ X) (hx : x ≫ p = 𝟙 _) (hx' : x' ≫ p = 𝟙 _)
    (hne : (fun i : ℤ ↦ W.cycleClass (ofOverField p hp) i (rationalPointClass p hp x hx i)) ≠
      fun i : ℤ ↦ W.cycleClass (ofOverField p hp) i (rationalPointClass p hp x' hx' i))
    (n : ℤ) (hn : 1 < n) (c : chowGroup (fieldChowSituation k') p 0) :
    rationalPointChowClass k' p x hx - rationalPointChowClass k' p x' hx' ≠ n • c := by
  have : Smooth (show (ofOverField (k := k) p hp).obj.left ⟶ (fieldChowSituation k').S from p) :=
    ‹Smooth p›
  exact W.rationalPointChowClass_sub_ne_zsmul_of_hypotheses hA hB hC
    (fun Z hZ ↦ finiteDimensional_H0_of_dimension_zero hA hB hC
      (SmoothProjectiveScheme.topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional hZ))
    (fun Z hZ ↦ isSeparable_H0_of_dimension_zero hA hB hC
      (SmoothProjectiveScheme.topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional hZ))
    (fun Z hZ c ↦ traceZero_eq_trace hA hB hC
      (SmoothProjectiveScheme.topologicalKrullDim_eq_zero_of_isNonemptyEquidimensional hZ) c)
    (ofOverField p hp) p hp rfl x x' hx hx' hne n hn c

end WeilData

end Stacks.WeilCohomology

end
