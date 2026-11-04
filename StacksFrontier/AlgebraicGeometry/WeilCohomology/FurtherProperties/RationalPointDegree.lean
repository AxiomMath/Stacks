module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.FurtherProperties.RationalPoints
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.DegreeHomomorphism
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ProductOfPuncturedSchemes
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantDisjoint.RestrictPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.OpenImmersionRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinConstruction.IntegralComponent

/-!
# The zero cycle of a rational point, and its degree on an open and closed piece

Let `X` be a scheme locally of finite type over a field `k` and `x` a `k`-rational point of
`X`, that is a section of the structure morphism. The cycle `[x]` is the prime cycle of the
image point with coefficient one. For an open and closed subscheme `U ⊆ X` that is proper over
`k`, restricting a zero cycle to `U` and taking its degree is a homomorphism `CH_0(X) ⟶ ℤ`,
which is one on `[x]` when `x ∈ U` and zero when `x ∉ U`. So if `x ∈ U` and `x' ∉ U`, the
difference `[x] - [x']` has degree one on `U` and is divisible by no integer `n > 1`: this is the
first sentence of the proof of Stacks 0FHU, the case of rational points on distinct components.

## Main definitions

* `Stacks.WeilCohomology.rationalPointLocus`: the point of `X` at which a rational point lies.
* `Stacks.WeilCohomology.opensDegree`: the degree of the restriction to an open subscheme
  proper over the base field.

## Main results

* `Stacks.WeilCohomology.rationalPointCycle_val`: `[x]` is the prime cycle of its locus.
* `Stacks.WeilCohomology.opensDegree_rationalPointChowClass`: the degree on `U` of `[x]`.
* `Stacks.WeilCohomology.rationalPointChowClass_sub_ne_zsmul_of_mem_of_notMem`: the
  indivisibility of `[x] - [x']` when an open subscheme proper over `k` contains `x` but not `x'`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.WeilCohomology

open Stacks.Chow

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ (fieldChowSituation k).S)

/-- **The locus of a rational point**: the point of `X` at which the section
`x : Spec k ⟶ X` lands, the image of the unique point of `Spec k`. -/
def rationalPointLocus (x : (fieldChowSituation k).S ⟶ X) : X :=
  x.base (genericPoint (fieldChowSituation k).S)

/-- The dimension function of the base situation of a field vanishes. -/
theorem fieldChowSituation_dimensionFunction_apply (s : (fieldChowSituation k).S) :
    (fieldChowSituation k).dimensionFunction s = 0 :=
  rfl

/-- The locus of a rational point has relative dimension zero over the field. -/
theorem relativeDimension_rationalPointLocus (x : (fieldChowSituation k).S ⟶ X)
    [IsClosedImmersion x] (hx : x ≫ p = 𝟙 (fieldChowSituation k).S) :
    relativeDimension (fieldChowSituation k).dimensionFunction p (rationalPointLocus x) = 0 := by
  rw [rationalPointLocus, ← relativeDimension_comp_closedImmersion, hx, relativeDimension_id]
  rfl

variable [LocallyOfFiniteType p]

/-- **The cycle of a rational point is the prime cycle of its locus**, with coefficient one:
`Spec k` is integral with a single point, its multiplicity there is one, and that point has
relative dimension zero. -/
theorem rationalPointCycle_val (x : (fieldChowSituation k).S ⟶ X)
    [IsClosedImmersion x] (hx : x ≫ p = 𝟙 (fieldChowSituation k).S) :
    (cycleAssociatedToClosedSubscheme (fieldChowSituation k) p x 0).1 =
      @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        (rationalPointLocus x) 1 := by
  classical
  have hmem : genericPoint (fieldChowSituation k).S ∈ genericPoints (fieldChowSituation k).S :=
    genericPoint_mem_genericPoints _
  ext y
  by_cases hy : y = rationalPointLocus x
  · subst hy
    rw [show rationalPointLocus x = x.base (⟨_, hmem⟩ : genericPoints _).1 from rfl,
      cycleAssociatedToClosedSubscheme_apply (fieldChowSituation k) p x 0 ⟨_, hmem⟩
      (relativeDimension_rationalPointLocus p x hx), componentMultiplicity_eq_one x hmem]
    simp
  · rw [cycleAssociatedToClosedSubscheme_apply_eq_zero]
    · simp [hy]
    · rintro ⟨ξ, hξ, -⟩
      exact hy (hξ ▸ congrArg x.base (Subsingleton.elim _ _))

/-- **The class of a rational point** is the class of the prime cycle of its locus. -/
theorem rationalPointChowClass_val (x : (fieldChowSituation k).S ⟶ X)
    (hx : x ≫ p = 𝟙 (fieldChowSituation k).S) :
    ∃ α : CycleGroup (fieldChowSituation k) p 0,
      α.1 = @Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
        (rationalPointLocus x) 1 ∧
      rationalPointChowClass k p x hx =
        QuotientAddGroup.mk' (rationalEquivalences (fieldChowSituation k) p 0) α := by
  let : IsClosedImmersion x := isClosedImmersion_of_comp_eq_id p x hx
  exact ⟨_, rationalPointCycle_val p x hx, rfl⟩

/-! ### The degree on an open piece -/

/-- **The degree of the restriction to an open subscheme** `U ⊆ X` that is proper over the field:
restriction of zero cycles to `U`, which respects rational equivalence by Stacks 02S1 for an open
immersion, followed by the degree homomorphism of Stacks 0AZ1 on `U`. -/
def opensDegree (U : X.Opens) [IsProper (U.ι ≫ p)] :
    chowGroup (fieldChowSituation k) p 0 →+ ℤ :=
  (chowDegree (fieldChowSituation k) fieldChowSituation_dimensionFunction_apply (U.ι ≫ p)
      (genericPoint (fieldChowSituation k).S)).comp
    (chowGroupOpensRestrict (fieldChowSituation k) p U 0
      (flatPullbackFactorsThroughRationalEquivalence_of_opensι (fieldChowSituation k) p U 0))

/-- The degree on `U` of the class of a rational point is the degree of the restriction to `U` of
a cycle representing it, namely the prime cycle of its locus. -/
private theorem opensDegree_rationalPointChowClass_eq (U : X.Opens) [IsProper (U.ι ≫ p)]
    (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ p = 𝟙 (fieldChowSituation k).S) :
    ∃ α : CycleGroup (fieldChowSituation k) p 0,
      (∀ z : (U : Scheme.{u}),
        (cycleGroupOpensRestrict (fieldChowSituation k) p U 0 α).1 z =
          (@Function.locallyFinsuppWithin.single X _ ℤ (Classical.decEq X) _
            (rationalPointLocus x) 1) (U.ι.base z)) ∧
      opensDegree p U (rationalPointChowClass k p x hx) =
        cycleDegree (fieldChowSituation k) (U.ι ≫ p) (genericPoint (fieldChowSituation k).S)
          (cycleGroupOpensRestrict (fieldChowSituation k) p U 0 α) := by
  obtain ⟨α, hα, hcl⟩ := rationalPointChowClass_val p x hx
  refine ⟨α, fun z ↦ by rw [cycleGroupOpensRestrict_apply, hα], ?_⟩
  rw [hcl, opensDegree, AddMonoidHom.comp_apply, chowGroupOpensRestrict_mk, chowDegree_mk]

/-- **The degree on `U` of the class of a rational point lying in `U`** is one. -/
theorem opensDegree_rationalPointChowClass_of_mem (U : X.Opens) [IsProper (U.ι ≫ p)]
    (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ p = 𝟙 (fieldChowSituation k).S)
    (hU : rationalPointLocus x ∈ U) :
    opensDegree p U (rationalPointChowClass k p x hx) = 1 := by
  classical
  obtain ⟨α, hα, hdeg⟩ := opensDegree_rationalPointChowClass_eq p U x hx
  rw [hdeg]
  set y : (U : Scheme.{u}) := ⟨rationalPointLocus x, hU⟩
  have hres : (cycleGroupOpensRestrict (fieldChowSituation k) p U 0 α).1 =
      @Function.locallyFinsuppWithin.single (U : Scheme.{u}) _ ℤ (Classical.decEq _) _ y 1 := by
    ext z
    rw [hα, Function.locallyFinsuppWithin.single_apply, Function.locallyFinsuppWithin.single_apply]
    exact if_congr ⟨fun h ↦ Subtype.ext h, fun h ↦ by rw [h]; rfl⟩ rfl rfl
  rw [Subsingleton.elim (genericPoint (fieldChowSituation k).S) ((U.ι ≫ p).base y),
    cycleDegree_single (fieldChowSituation k) fieldChowSituation_dimensionFunction_apply
      (U.ι ≫ p) y _ hres, residueDegree_isOpenImmersion_comp U.ι p y,
    show U.ι.base y = x.base (genericPoint (fieldChowSituation k).S) from rfl,
    (residueDegree_eq_one_of_section p x hx _).1, Nat.cast_one]

/-- **The degree on `U` of the class of a rational point not lying in `U`** is zero. -/
theorem opensDegree_rationalPointChowClass_of_notMem (U : X.Opens) [IsProper (U.ι ≫ p)]
    (x : (fieldChowSituation k).S ⟶ X) (hx : x ≫ p = 𝟙 (fieldChowSituation k).S)
    (hU : rationalPointLocus x ∉ U) :
    opensDegree p U (rationalPointChowClass k p x hx) = 0 := by
  obtain ⟨α, hα, hdeg⟩ := opensDegree_rationalPointChowClass_eq p U x hx
  rw [hdeg]
  have hres : cycleGroupOpensRestrict (fieldChowSituation k) p U 0 α = 0 := by
    ext z
    rw [hα]
    have : U.ι.base z ≠ rationalPointLocus x := fun h ↦ hU (h ▸ z.2)
    simp [this]
  rw [hres, map_zero]

/-- **Rational points on distinct pieces.** If an open subscheme `U ⊆ X` proper over `k`
contains the locus of the rational point `x` but not that of `x'`, then `[x] - [x']` is divisible
by no integer `n > 1` in `CH_0(X)`: its degree on `U` is one. -/
theorem rationalPointChowClass_sub_ne_zsmul_of_mem_of_notMem (U : X.Opens) [IsProper (U.ι ≫ p)]
    (x x' : (fieldChowSituation k).S ⟶ X) (hx : x ≫ p = 𝟙 (fieldChowSituation k).S)
    (hx' : x' ≫ p = 𝟙 (fieldChowSituation k).S) (hxU : rationalPointLocus x ∈ U)
    (hx'U : rationalPointLocus x' ∉ U) (n : ℤ) (hn : 1 < n)
    (c : chowGroup (fieldChowSituation k) p 0) :
    rationalPointChowClass k p x hx - rationalPointChowClass k p x' hx' ≠ n • c := by
  intro h
  have hdeg := congrArg (opensDegree p U) h
  rw [map_sub, map_zsmul, opensDegree_rationalPointChowClass_of_mem p U x hx hxU,
    opensDegree_rationalPointChowClass_of_notMem p U x' hx' hx'U, sub_zero, smul_eq_mul] at hdeg
  have hdvd : n ∣ 1 := ⟨_, hdeg⟩
  have := Int.le_of_dvd one_pos hdvd
  omega

end Stacks.WeilCohomology

end
