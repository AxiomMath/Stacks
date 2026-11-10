module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalTheory
public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.TowerProjective
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ClassicalChowCycleData
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Concrete.CycleClassFundamental
public import StacksFrontier.AlgebraicGeometry.Morphisms.Projective.AffineBase
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.SmoothProjectiveComposition

/-!
# The trace of the cycle class of a zero cycle

Stacks 0FGW: for a classical Weil cohomology theory and a smooth projective variety `X` of
dimension `d`, the diagram

  `CH^d(X) --γ--> H^{2d}(X) --∫_X--> F`,  `CH^d(X) = CH_0(X) --deg--> ℤ → F`

commutes, where `deg` is the degree of zero cycles of Chow Homology, Section 0AZ0.

The proof is the source's. By axiom `(C)(b)` for the structure morphism `π : X ⟶ Spec k`,
`∫_X γ(α) = ∫_{Spec k} γ(π_*α)`, and `π_*α = deg(α)·[Spec k]` (Stacks 0AZ1); axiom `(C)(d)`,
`∫_{Spec k} γ([Spec k]) = 1`, finishes. The first step holds for the abstract cycle data of
`Stacks.WeilCohomology.ClassicalWeilCohomologyTheory` and is proved there; the statement of
the tag is for the theory on the Chow groups of Chapter 42,
`Stacks.WeilCohomology.ChowClassicalWeilCohomologyTheory`.

## Main definitions

All names below are in the namespace `Stacks.WeilCohomology`.

* `SmoothProjective.specPoint`: `Spec k` as a smooth projective variety.
* `SmoothProjective.toSpecPoint`: the structure morphism `X ⟶ Spec k`.

## Main results

* `PoincareDualityPushforwardSetup.integration_eq_integration_pushforward`:
  `∫_X a = ∫_Y f_*a` for a top-degree class `a` on `X`.
* `ClassicalWeilCohomologyTheory.integration_cycleClass_eq_integration_cycleClass_pushforward`:
  `∫_X γ(α) = ∫_Y γ(f_*α)` for `α ∈ CH^{dim X}(X)`.
* `integration_cycleClass_codimensionClassOfZeroCycle`: **Stacks 0FGW**,
  `∫_X γ(α) = deg(α)` for a zero cycle class `α` on `X`.

## Implementation notes

The Chow groups of Chapter 42 graded by codimension are `CH^d(X) = ∏_e CH_{e-d}(X_e)`, the
product over the open and closed parts `X_e` of `X` of dimension `e`
(`Stacks.Chow.codimensionChowGroup`). A variety of dimension `d` is its own part `X_d`, so the
identification `CH^d(X) = CH_0(X)` of the source is
`Stacks.WeilCohomology.codimensionClassOfZeroCycle` on `CH_0(X_d)`, and the degree is
`Stacks.Chow.chowDegree` on `CH_0(X_d)`.

## References

* [Stacks Project, Tag 0FGW](https://stacks.math.columbia.edu/tag/0FGW)
* [Stacks Project, Tag 0AZ1](https://stacks.math.columbia.edu/tag/0AZ1)
-/

open AlgebraicGeometry

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u v w t

namespace Stacks.WeilCohomology

variable {k : Type u} [Field k] [IsAlgClosed k] {F : Type v} [Field F] [CharZero F]
  {X Y : (SmoothProjective k).FullSubcategory}

/-- The point `Spec k` as a smooth projective variety over `k`: its structure morphism is the
identity. -/
noncomputable abbrev SmoothProjective.specPoint (k : Type u) [Field k] :
    (SmoothProjective k).FullSubcategory :=
  ⟨Over.mk (𝟙 (Spec (.of k))),
    ⟨(isSmoothVariety_iff k (𝟙 (Spec (.of k)))).2 ⟨by constructor,
      inferInstance⟩, isProjectiveMorphism_id _⟩⟩

/-- The structure morphism of the point is an isomorphism. -/
instance SmoothProjective.isIso_specPoint_hom (k : Type u) [Field k] :
    IsIso (SmoothProjective.specPoint k).obj.hom :=
  inferInstanceAs (IsIso (𝟙 (Spec (.of k))))

/-- The point has dimension zero. -/
theorem SmoothProjective.topologicalKrullDim_specPoint (k : Type u) [Field k] :
    topologicalKrullDim (SmoothProjective.specPoint k).obj.left = 0 := by
  change topologicalKrullDim (PrimeSpectrum k) = 0
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_isField
    (Field.toIsField k)]

/-- The structure morphism of a smooth projective variety, as a morphism to the point. -/
noncomputable def SmoothProjective.toSpecPoint (X : (SmoothProjective k).FullSubcategory) :
    X ⟶ SmoothProjective.specPoint k :=
  ObjectProperty.homMk (Over.homMk X.obj.hom (by simp [SmoothProjective.specPoint]))

namespace PoincareDualityPushforwardSetup

variable (S : PoincareDualityPushforwardSetup.{u, v, w} k F)

/-- The Poincaré-duality pushforward respects transport of its degree argument. -/
theorem pushforward_heq (f : X ⟶ Y) {i i' : ℤ} (h : i = i')
    {x : (S.H X).piece (2 * (S.dimension X : ℤ) - i)}
    {x' : (S.H X).piece (2 * (S.dimension X : ℤ) - i')} (hx : x ≍ x') :
    S.pushforward f i x ≍ S.pushforward f i' x' := by
  subst h
  cases hx
  rfl

/-- The trace is compatible with pushforward: `∫_X a = ∫_Y f_*a` for a class `a` of top degree on
`X`, the pushforward being the one in degree `0` determined by Poincaré duality. This is the
trace equation `∫_X f^*1 ∪ a = ∫_Y 1 ∪ f_*a` defining the pushforward. -/
theorem integration_eq_integration_pushforward (f : X ⟶ Y)
    (a : (S.H X).piece (2 * (S.dimension X : ℤ))) :
    S.integration X a =
      S.integration Y
        (ExternallyGraded.degreeCast (R := F) (X := (S.H Y).piece)
          (sub_zero (2 * (S.dimension Y : ℤ)))
          (S.pushforward f 0
            (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
              (sub_zero (2 * (S.dimension X : ℤ))).symm a))) := by
  have key := S.integration_pullback_mul f 0 (S.H Y).one
    (ExternallyGraded.degreeCast (R := F) (X := (S.H X).piece)
      (sub_zero (2 * (S.dimension X : ℤ))).symm a)
  rw [S.pullback_one] at key
  simp only [ExternallyGradedAlgebra.tracePairing, LinearMap.compr₂_apply,
    LinearEquiv.coe_coe, LinearMap.comp_apply] at key
  convert key using 2 <;> apply eq_of_heq
  · exact ((ExternallyGraded.degreeCast_heq (R := F) _ _).trans
      (((S.H X).one_mul _ _).trans (ExternallyGraded.degreeCast_heq (R := F) _ _))).symm
  · exact (ExternallyGraded.degreeCast_heq (R := F) _ _).trans
      (((S.H Y).one_mul _ _).symm.trans (ExternallyGraded.degreeCast_heq (R := F) _ _).symm)

end PoincareDualityPushforwardSetup

namespace ClassicalWeilCohomologyTheory

variable {Ch : ChowCycleData.{u, t} k} (T : ClassicalWeilCohomologyTheory.{u, v, w, t} k F Ch)

/-- The trace of the cycle class of a cycle of top codimension is the trace of the cycle class of
its pushforward: `∫_X γ(α) = ∫_Y γ(f_*α)` for `α ∈ CH^{dim X}(X)`, by axiom `(C)(b)`. -/
theorem integration_cycleClass_eq_integration_cycleClass_pushforward (f : X ⟶ Y)
    (α : Ch.group X (T.dimension X)) :
    T.integration X (T.cycleClass X (T.dimension X) α) =
      T.integration Y
        (ExternallyGraded.degreeCast (R := F) (X := (T.H Y).piece)
          (show 2 * ((T.dimension X : ℤ) + (T.dimension Y : ℤ) - (T.dimension X : ℤ)) =
              2 * (T.dimension Y : ℤ) by ring)
          (T.cycleClass Y ((T.dimension X : ℤ) + (T.dimension Y : ℤ) - (T.dimension X : ℤ))
            (Ch.pushforward f (T.dimension X) (T.dimension Y) (T.dimension_eq X)
              (T.dimension_eq Y) (T.dimension X) α))) := by
  rw [T.toPoincareDualityPushforwardSetup.integration_eq_integration_pushforward f]
  congr 1
  apply eq_of_heq
  refine (ExternallyGraded.degreeCast_heq (R := F) _ _).trans ?_
  refine HEq.trans ?_ (ExternallyGraded.degreeCast_heq (R := F) (X := (T.H Y).piece) _ _).symm
  refine (T.toPoincareDualityPushforwardSetup.pushforward_heq f
    (show (0 : ℤ) = 2 * (T.dimension X : ℤ) - 2 * (T.dimension X : ℤ) by ring)
    ((ExternallyGraded.degreeCast_heq (R := F) _ _).trans
      (ExternallyGraded.degreeCast_heq (R := F)
        (show 2 * (T.dimension X : ℤ) = 2 * (T.dimension X : ℤ) -
          (2 * (T.dimension X : ℤ) - 2 * (T.dimension X : ℤ)) by ring) _).symm)).trans ?_
  rw [T.cycleClass_pushforward]
  exact ExternallyGraded.degreeCast_heq (R := F) _ _

/-- The recorded dimension of the point is zero. -/
theorem dimension_specPoint : T.dimension (SmoothProjective.specPoint k) = 0 := by
  have h := T.dimension_eq (SmoothProjective.specPoint k)
  rw [SmoothProjective.topologicalKrullDim_specPoint] at h
  exact_mod_cast h.symm

/-- The cycle class map respects transport of the codimension. -/
theorem cycleClass_heq (Z : (SmoothProjective k).FullSubcategory) {r r' : ℤ} (h : r = r')
    {c : Ch.group Z r} {c' : Ch.group Z r'} (hc : c ≍ c') :
    T.cycleClass Z r c ≍ T.cycleClass Z r' c' := by
  subst h
  cases hc
  rfl

end ClassicalWeilCohomologyTheory

/-! ### Stacks 0FGW -/

section ChowCycles

open Stacks.Chow

omit [IsAlgClosed k] in
/-- The point of the smooth projective varieties is the point of the smooth projective schemes. -/
theorem toSchemeCat_obj_specPoint :
    (SmoothProjective.toSchemeCat k).obj (SmoothProjective.specPoint k) =
      SmoothProjectiveScheme.point k :=
  rfl

omit [IsAlgClosed k] in
/-- The pushforward between equidimensional schemes respects transport of the dimension of the
target and of the codimension of the image. -/
theorem equidimensionalPushforward_heq {X' Y' : (SmoothProjectiveScheme k).FullSubcategory}
    (f : X' ⟶ Y') (d : ℕ) {e e' : ℕ} (he : e = e') (p : ℤ) {q q' : ℤ} (hq : q = p + e - d)
    (hq' : q' = p + e' - d) (α : codimensionChowGroup k X'.obj.hom p) :
    equidimensionalPushforward f d e p q hq α ≍ equidimensionalPushforward f d e' p q' hq' α := by
  subst he hq hq'
  rfl

variable (T : ChowClassicalWeilCohomologyTheory k F)

/-- **Stacks Project, Tag 0FGW.** Let `X` be a smooth projective variety of dimension `d`. Then
`∫_X γ(α) = deg(α)` for every zero cycle class `α ∈ CH_0(X) = CH^d(X)`: the composite
`CH^d(X) → H^{2d}(X) → F` of the cycle class map and the trace is the degree of zero cycles
(Chow Homology, Section 0AZ0) followed by `ℤ → F`.

Chow groups graded by codimension are `CH^d(X) = ∏_e CH_{e-d}(X_e)`, the product over the open
and closed parts `X_e` of `X` of dimension `e`; a variety of dimension `d` is its own part `X_d`,
so a zero cycle class on `X` is a class `α ∈ CH_0(X_d)`, and its class in `CH^d(X)` is
`Stacks.WeilCohomology.codimensionClassOfZeroCycle α`. The degree is `Stacks.Chow.chowDegree`
(Stacks 0AZ1). -/
@[stacks 0FGW]
theorem integration_cycleClass_codimensionClassOfZeroCycle
    (X : (SmoothProjective k).FullSubcategory)
    (α : chowGroup (fieldChowSituation k)
      (partBase ((SmoothProjective.toSchemeCat k).obj X).obj.hom (T.dimension X)) 0) :
    haveI := (isClopenDecomposition_dimPart
      ((SmoothProjective.toSchemeCat k).obj X).obj.hom).isProper_ι (T.dimension X)
    T.integration X (T.cycleClass X (T.dimension X)
        (codimensionClassOfZeroCycle (X := (SmoothProjective.toSchemeCat k).obj X) α)) =
      (chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction k)
        (partBase ((SmoothProjective.toSchemeCat k).obj X).obj.hom (T.dimension X)) default α :
        F) := by
  have := (isClopenDecomposition_dimPart
    ((SmoothProjective.toSchemeCat k).obj X).obj.hom).isProper_ι (T.dimension X)
  let n := chowDegree (fieldChowSituation k) (fieldChowSituation_dimensionFunction k)
    (partBase ((SmoothProjective.toSchemeCat k).obj X).obj.hom (T.dimension X)) default α
  have hP := T.dimension_specPoint
  have hpush := equidimensionalPushforward_codimensionClassOfZeroCycle
    (fieldChowSituation_dimensionFunction k) default α
  refine (T.integration_cycleClass_eq_integration_cycleClass_pushforward
    (SmoothProjective.toSpecPoint X) _).trans ?_
  have hnorm := T.integration_cycleClass_fundamental (SmoothProjective.specPoint k)
    inferInstance hP
  have key : ExternallyGraded.degreeCast (R := F)
        (X := (T.H (SmoothProjective.specPoint k)).piece)
        (show 2 * ((T.dimension X : ℤ) + (T.dimension (SmoothProjective.specPoint k) : ℤ) -
            (T.dimension X : ℤ)) = 2 * (T.dimension (SmoothProjective.specPoint k) : ℤ) by ring)
        (T.cycleClass (SmoothProjective.specPoint k)
          ((T.dimension X : ℤ) + (T.dimension (SmoothProjective.specPoint k) : ℤ) -
            (T.dimension X : ℤ))
          ((chowCycleData k).pushforward (SmoothProjective.toSpecPoint X) (T.dimension X)
            (T.dimension (SmoothProjective.specPoint k)) (T.dimension_eq X)
            (T.dimension_eq (SmoothProjective.specPoint k)) (T.dimension X)
            (codimensionClassOfZeroCycle (X := (SmoothProjective.toSchemeCat k).obj X) α))) =
      n • ExternallyGraded.degreeCast (R := F) (X := (T.H (SmoothProjective.specPoint k)).piece)
        (show 2 * (0 : ℤ) = 2 * (T.dimension (SmoothProjective.specPoint k) : ℤ) by omega)
        (T.cycleClass (SmoothProjective.specPoint k) 0
          ((chowCycleData k).fundamental (SmoothProjective.specPoint k))) := by
    rw [← map_zsmul, ← map_zsmul]
    apply eq_of_heq
    refine (ExternallyGraded.degreeCast_heq (R := F) _ _).trans ?_
    refine HEq.trans ?_ (ExternallyGraded.degreeCast_heq (R := F) _ _).symm
    refine T.cycleClass_heq _ (by omega) ?_
    refine (equidimensionalPushforward_heq _ (T.dimension X) hP (T.dimension X) rfl
      (show (0 : ℤ) = (T.dimension X : ℤ) + ((0 : ℕ) : ℤ) - (T.dimension X : ℤ) by simp)
      _).trans ?_
    exact heq_of_eq hpush
  rw [key, map_zsmul, hnorm, zsmul_one]

end ChowCycles

end Stacks.WeilCohomology

end
