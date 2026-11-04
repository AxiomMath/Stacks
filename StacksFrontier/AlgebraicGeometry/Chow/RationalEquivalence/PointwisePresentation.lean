module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.KeyLemma.MilnorKDegreeOne
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseCycles
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalence.PointwiseDivisor
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksCore.Tactic.StacksAttribute

/-!
# The Chow group as a quotient of pointwise Milnor K-chains

Let `(S, δ)` be the base situation of chapter 42 and `p : X ⟶ S` locally of finite type. Stacks
0GU3 presents the Chow group `A_k(X)` as a quotient of the group of locally finite families of
degree-zero Milnor K-classes at the points of relative dimension `k`: the class map is the
composite of the identification `Stacks.Chow.pointwiseCycleEquiv` of that group with `Z_k(X)`
and the projection `Z_k(X) ↠ A_k(X)`.

This file provides the class map, its surjectivity, and the exactness of the presentation in
the middle: the image of the divisor differential
`Stacks.Chow.pointwiseDivisorDifferential` is the kernel of the class map. One inclusion is
immediate from the construction of the differential, which is a locally finite sum of
pushed-forward principal divisors; the other requires producing, from a presentation of a cycle
as such a sum, a single pointwise Milnor K₁-chain with that cycle as its divisor. The class of
that chain at a point `x` of relative dimension `k + 1` is the product of the values at `x` of
the rational functions of those members of the given family whose generic point is `x`: the
family may present one point several times, or present it by an integral closed subscheme other
than `closure {x}`, and both are absorbed by passing to the value at the generic point.

## Main definitions

* `Stacks.Chow.pointwiseChowClass` — the class in `A_k(X)` of a pointwise Milnor K₀ chain
  (Stacks 0GU3).
* `Stacks.Chow.familyResidueFieldUnit` — the product of the values at a point of the rational
  functions of a family of integral closed subschemes with that generic point.
* `Stacks.Chow.pointwiseChainOfFamily` — the pointwise Milnor K₁-chain attached to a locally
  finite family of integral closed subschemes carrying nonzero rational functions.

## Main results

* `Stacks.Chow.pointwiseChowClass_surjective` — every Chow class has a pointwise representative
  (Stacks 0GU3).
* `Stacks.Chow.pointwiseChowClass_mem_ker_iff` — a pointwise chain is in the kernel exactly when
  the cycle it names is rationally equivalent to zero.
* `Stacks.Chow.principalDivisorPushforward_eq_of_value_eq` — the pushed-forward principal
  divisor of a nonzero rational function on an integral closed subscheme depends only on the
  generic point of the subscheme and the value of the function there.
* `Stacks.Chow.pointwiseDivisorSum_pointwiseChainOfFamily` — the divisor of the chain attached
  to a locally finite family is the cycle of that family.
* `Stacks.Chow.pointwiseDivisorDifferential_range_eq_ker_pointwiseChowClass` — exactness of the
  presentation (Stacks 0GU3).

## References

* [Stacks Project, Tag 0GU2](https://stacks.math.columbia.edu/tag/0GU2)
* [Stacks Project, Tag 0GU3](https://stacks.math.columbia.edu/tag/0GU3)
* [Stacks Project, Tag 02RP](https://stacks.math.columbia.edu/tag/02RP)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p]

/-- **Stacks 0GU3.** The class in the Chow group `A_k(X)` of a locally finite family of
degree-zero Milnor K-classes at the points of relative dimension `k`: the cycle it names,
modulo rational equivalence. -/
@[stacks 0GU3 "the map from pointwise cycles to the Chow group"]
def pointwiseChowClass (k : ℤ) : PointwiseCycleGroup C p k →+ chowGroup C p k :=
  (QuotientAddGroup.mk' (rationalEquivalences C p k)).comp
    (pointwiseCycleEquiv C p k).symm.toAddMonoidHom

/-- A pointwise Milnor K₀ chain has vanishing Chow class exactly when the cycle it names is
rationally equivalent to zero. -/
theorem pointwiseChowClass_mem_ker_iff (k : ℤ) (b : PointwiseCycleGroup C p k) :
    b ∈ (pointwiseChowClass C p k).ker ↔
      (pointwiseCycleEquiv C p k).symm b ∈ rationalEquivalences C p k := by
  rw [AddMonoidHom.mem_ker]
  change QuotientAddGroup.mk' (rationalEquivalences C p k)
      ((pointwiseCycleEquiv C p k).symm b) = 0 ↔ _
  exact QuotientAddGroup.eq_zero_iff _

/-- **Stacks 0GU3.** Every class in the Chow group `A_k(X)` is the class of a pointwise Milnor
K₀ chain: the chain attached to any cycle representing it. -/
@[stacks 0GU3 "surjectivity of the presentation"]
theorem pointwiseChowClass_surjective (k : ℤ) :
    Function.Surjective (pointwiseChowClass C p k) := by
  intro q
  obtain ⟨α, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C p k) q
  exact ⟨pointwiseCycleEquiv C p k α, by simp [pointwiseChowClass]⟩

/-! ### Locally finite families of integral closed subschemes -/

/-- A locally finite family of integral closed subschemes has finite fibres over the points of
`X`: only finitely many members have a prescribed generic point. -/
theorem finite_genericPointOf_eq {ι : Type*} (W : ι → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (x : X) :
    {j | genericPointOf (W j) (hW j) = x}.Finite := by
  refine finite_fiber_of_locallyFinite (σ := fun j ↦ genericPointOf (W j) (hW j)) ?_ x
  rw [show (fun j ↦ closure ({genericPointOf (W j) (hW j)} : Set X)) =
    fun j ↦ ((W j).support : Set X) from
      funext fun j ↦ (support_eq_closure_genericPointOf (W j) (hW j)).symm]
  exact hLocal

/-- Only finitely many members of a locally finite family of integral closed subschemes contain
a prescribed point of `X`. -/
theorem finite_mem_support_of_locallyFinite {ι : Type*} (W : ι → X.IdealSheafData)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X)) (x : X) :
    {j | x ∈ ((W j).support : Set X)}.Finite := by
  obtain ⟨t, ht, hfin⟩ := hLocal x
  exact hfin.subset fun j hj ↦ ⟨x, hj, mem_of_mem_nhds ht⟩

/-- Reading units of the residue field at `x` as nonzero rational functions on `closure {x}`
turns a finite product into a finite product. -/
theorem integralComponentFunction_prod (x : X) {ι : Type*} (u : ι → (X.residueField x)ˣ)
    (s : Finset ι) :
    integralComponentFunction x (∏ i ∈ s, u i) =
      ∏ i ∈ s, integralComponentFunction x (u i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi, integralComponentFunction_mul, ih]

/-! ### Products of rational functions and sums of principal divisors -/

/-- The coefficient at a point of a finite sum of cycles is the sum of the coefficients. -/
theorem algebraicCycle_sum_apply {ι : Type*} (c : ι → AlgebraicCycle X ℤ) (s : Finset ι)
    (y : X) : (∑ i ∈ s, c i) y = ∑ i ∈ s, c i y := by
  rw [Function.locallyFinsuppWithin.coe_sum, Finset.sum_apply]

/-- **Stacks 02RP after pushforward.** The pushforward of the principal divisor of a finite
product of nonzero rational functions is the sum of the pushforwards of the principal divisors
of the factors. -/
theorem principalDivisorPushforward_prod (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    {ι : Type*} (q : ι → (rationalFunctions V.subscheme)ˣ) (s : Finset ι) :
    principalDivisorPushforward C p V hV (∏ j ∈ s, q j) =
      ∑ j ∈ s, principalDivisorPushforward C p V hV (q j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, principalDivisorPushforward_mul, ih]

/-- **The pushed-forward principal divisor only remembers a point and a value.** An integral
closed subscheme is the reduced induced structure on the closure of its generic point, and a
nonzero rational function on it is determined by its value there; so two nonzero rational
functions on integral closed subschemes with the same generic point and the same value there
have the same pushed-forward principal divisor. -/
theorem principalDivisorPushforward_eq_of_value_eq {V V' : X.IdealSheafData}
    (hV : IsIntegral V.subscheme) (hV' : IsIntegral V'.subscheme) {x : X}
    (hx : genericPointOf V hV = x) (hx' : genericPointOf V' hV' = x)
    (g : (rationalFunctions V.subscheme)ˣ) (g' : (rationalFunctions V'.subscheme)ˣ)
    (hval : rationalFunctionUnitsEquivOfGenericPoint V hV hx g =
      rationalFunctionUnitsEquivOfGenericPoint V' hV' hx' g') :
    principalDivisorPushforward C p V hV g = principalDivisorPushforward C p V' hV' g' := by
  have hVV' : V = V' :=
    calc V = integralComponentAt (genericPointOf V hV) :=
          (integralComponentAt_genericPointOf V hV).symm
      _ = integralComponentAt x := by rw [hx]
      _ = integralComponentAt (genericPointOf V' hV') := by rw [hx']
      _ = V' := integralComponentAt_genericPointOf V' hV'
  subst hVV'
  exact congrArg (principalDivisorPushforward C p V hV)
    ((rationalFunctionUnitsEquivOfGenericPoint V hV hx).injective hval)

/-- **The pushed-forward principal divisor is computed on the closure of the generic point.**
The divisor of a nonzero rational function `g` on an integral closed subscheme with generic
point `x` is the divisor of the rational function on `closure {x}` whose value at `x` is the
value of `g` there. -/
theorem principalDivisorPushforward_eq_integralComponentAt (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme) {x : X} (hx : genericPointOf V hV = x)
    (g : (rationalFunctions V.subscheme)ˣ) :
    principalDivisorPushforward C p V hV g =
      principalDivisorPushforward C p (integralComponentAt x)
        (isIntegral_integralComponentAt x)
        (integralComponentFunction x
          (rationalFunctionUnitsEquivOfGenericPoint V hV hx g)) :=
  principalDivisorPushforward_eq_of_value_eq C p hV (isIntegral_integralComponentAt x) hx
    (genericPointOf_integralComponentAt x) g _ (integralComponentFunction_value x _).symm

/-! ### The pointwise chain attached to a locally finite family -/

/-- The product, over those members of a family of integral closed subschemes whose generic
point is `x`, of the values at `x` of their rational functions: a unit of the residue field of
`X` at `x`. For a locally finite family only finitely many members contribute. -/
def familyResidueFieldUnit {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (x : X) : (X.residueField x)ˣ :=
  ∏ᶠ j : {j : J // genericPointOf (W j) (hW j) = x},
    rationalFunctionUnitsEquivOfGenericPoint (W j.1) (hW j.1) j.2 (g j.1)

/-- Some member of the family has `x` as its generic point as soon as the product of the values
at `x` of the rational functions of the family is not `1`. -/
theorem exists_genericPointOf_eq_of_familyResidueFieldUnit_ne_one {J : Type u}
    (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) {x : X}
    (hx : familyResidueFieldUnit W hW g x ≠ 1) :
    ∃ j, genericPointOf (W j) (hW j) = x := by
  by_contra hno
  have : IsEmpty {j : J // genericPointOf (W j) (hW j) = x} :=
    ⟨fun j ↦ (not_exists.mp hno) j.1 j.2⟩
  exact hx (finprod_of_isEmpty _)

/-- On a finite fibre the defining product of `Stacks.Chow.familyResidueFieldUnit` is an honest
finite product. -/
theorem familyResidueFieldUnit_eq_prod {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (x : X)
    [Fintype {j : J // genericPointOf (W j) (hW j) = x}] :
    familyResidueFieldUnit W hW g x =
      ∏ j : {j : J // genericPointOf (W j) (hW j) = x},
        rationalFunctionUnitsEquivOfGenericPoint (W j.1) (hW j.1) j.2 (g j.1) :=
  finprod_eq_prod_of_fintype _

/-- The pointwise Milnor K₁-chain attached to a locally finite family of integral closed
subschemes carrying nonzero rational functions: its class at a point `x` of relative dimension
`k + 1` is the product of the values at `x` of the rational functions of those members of the
family whose generic point is `x`. -/
def pointwiseChainOfFamily (k : ℤ) {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) : PointwiseKOneGroup C p k :=
  ⟨fun x ↦ (milnorKTheoryOneAddEquiv (X.residueField x.1)).symm
      (Additive.ofMul (familyResidueFieldUnit W hW g x.1)), by
    intro U hU
    refine Set.Finite.of_finite_image (f := fun x : pointsOfDimension C p (k + 1) ↦ (x : X))
      (((hLocal.finite_nonempty_inter_compact hU).image
        fun j ↦ genericPointOf (W j) (hW j)).subset ?_)
      (Set.injOn_of_injective Subtype.val_injective)
    rintro _ ⟨x, ⟨hxU, hxne⟩, rfl⟩
    have hu : familyResidueFieldUnit W hW g x.1 ≠ 1 := fun h ↦ hxne (by simp [h])
    obtain ⟨j, hj⟩ := exists_genericPointOf_eq_of_familyResidueFieldUnit_ne_one W hW g hu
    refine ⟨j, ⟨x.1, ?_, hxU⟩, hj⟩
    show x.1 ∈ ((W j).support : Set X)
    rw [support_eq_closure_genericPointOf (W j) (hW j), hj]
    exact subset_closure (Set.mem_singleton _)⟩

omit [LocallyOfFiniteType p] in
/-- The Milnor K₁-class of the chain attached to a family, read as a unit of the residue
field. -/
@[simp]
theorem toMul_milnorKTheoryOneAddEquiv_pointwiseChainOfFamily (k : ℤ) {J : Type u}
    (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (x : pointsOfDimension C p (k + 1)) :
    Additive.toMul (milnorKTheoryOneAddEquiv (X.residueField x.1)
        ((pointwiseChainOfFamily C p k W hW hLocal g).1 x)) =
      familyResidueFieldUnit W hW g x.1 := by
  simp [pointwiseChainOfFamily]

omit [LocallyOfFiniteType p] in
/-- The chain attached to a family vanishes at a point exactly when the product of the values
there of the rational functions of the family is `1`. -/
theorem pointwiseChainOfFamily_eq_zero_iff (k : ℤ) {J : Type u} (W : J → X.IdealSheafData)
    (hW : ∀ j, IsIntegral (W j).subscheme)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (x : pointsOfDimension C p (k + 1)) :
    (pointwiseChainOfFamily C p k W hW hLocal g).1 x = 0 ↔
      familyResidueFieldUnit W hW g x.1 = 1 := by
  simp [pointwiseChainOfFamily]

/-- The contribution of a point `x` to the divisor of the chain attached to a family is the sum
of the contributions of those members of the family whose generic point is `x`. -/
theorem pointwiseDivisorTerm_pointwiseChainOfFamily (k : ℤ) {J : Type u}
    (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (x : pointsOfDimension C p (k + 1))
    [Fintype {j : J // genericPointOf (W j) (hW j) = x.1}] (y : X) :
    pointwiseDivisorTerm C p k (pointwiseChainOfFamily C p k W hW hLocal g) x y =
      ∑ j : {j : J // genericPointOf (W j) (hW j) = x.1},
        principalDivisorPushforward C p (W j.1) (hW j.1) (g j.1) y := by
  rw [pointwiseDivisorTerm, pointwiseComponentFunction,
    toMul_milnorKTheoryOneAddEquiv_pointwiseChainOfFamily,
    familyResidueFieldUnit_eq_prod, integralComponentFunction_prod,
    principalDivisorPushforward_prod, algebraicCycle_sum_apply]
  exact Finset.sum_congr rfl fun j _ ↦ congrArg (fun c : AlgebraicCycle X ℤ ↦ c y)
    (principalDivisorPushforward_eq_integralComponentAt C p (W j.1) (hW j.1) j.2 (g j.1)).symm

/-- A point lies in the support of an integral closed subscheme exactly when it lies in the
closure of its generic point. -/
private theorem mem_support_iff_mem_closure_of_genericPointOf_eq {W : X.IdealSheafData}
    (hW : IsIntegral W.subscheme) {x : X} (hx : genericPointOf W hW = x) (y : X) :
    y ∈ (W.support : Set X) ↔ y ∈ closure ({x} : Set X) := by
  rw [support_eq_closure_genericPointOf W hW, hx]

/-- If `y` lies in `closure {x}` and every member of the family whose support contains `y` is
indexed by `s`, the contribution of `x` at `y` to the divisor of the chain attached to the family
is the sum over the indices in `s` whose generic point is `x`. -/
private theorem pointwiseDivisorTerm_pointwiseChainOfFamily_eq_sum_filter (k : ℤ) {J : Type u}
    (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (x : pointsOfDimension C p (k + 1))
    [DecidablePred fun j ↦ genericPointOf (W j) (hW j) = x.1] {y : X}
    (hy : y ∈ closure ({x.1} : Set X)) (s : Finset J)
    (hs : ∀ j, y ∈ ((W j).support : Set X) → j ∈ s) :
    pointwiseDivisorTerm C p k (pointwiseChainOfFamily C p k W hW hLocal g) x y =
      ∑ j ∈ s.filter fun j ↦ genericPointOf (W j) (hW j) = x.1,
        principalDivisorPushforward C p (W j) (hW j) (g j) y := by
  have : Finite {j : J // genericPointOf (W j) (hW j) = x.1} :=
    Set.finite_coe_iff.mpr (finite_genericPointOf_eq W hW hLocal x.1)
  let _ : Fintype {j : J // genericPointOf (W j) (hW j) = x.1} := Fintype.ofFinite _
  have hsub : s.subtype (fun j ↦ genericPointOf (W j) (hW j) = x.1) = Finset.univ :=
    Finset.eq_univ_of_forall fun j ↦ Finset.mem_subtype.mpr <| hs j.1 <|
      (mem_support_iff_mem_closure_of_genericPointOf_eq (hW j.1) j.2 y).mpr hy
  rw [← Finset.sum_subtype_eq_sum_filter, hsub]
  exact pointwiseDivisorTerm_pointwiseChainOfFamily C p k W hW hLocal g x y

/-- **The divisor of the chain attached to a locally finite family is the cycle of that
family.** Both sides are locally finite sums of the pushed-forward principal divisors of the
same rational functions, grouped on the left by the generic points of the members of the
family. -/
theorem pointwiseDivisorSum_pointwiseChainOfFamily (k : ℤ) {J : Type u}
    (W : J → X.IdealSheafData) (hW : ∀ j, IsIntegral (W j).subscheme)
    (hDim : ∀ j, schemeDeltaDimension C ((W j).subschemeι ≫ p) = ((k + 1 : ℤ) : EInt))
    (hLocal : LocallyFinite fun j ↦ ((W j).support : Set X))
    (g : ∀ j, (rationalFunctions (W j).subscheme)ˣ) (y : X) :
    (pointwiseDivisorSum C p k (pointwiseChainOfFamily C p k W hW hLocal g)).1 y =
      principalDivisorFamilyCoefficient C p W hW g y := by
  classical
  set π : J → pointsOfDimension C p (k + 1) := fun j ↦
    ⟨genericPointOf (W j) (hW j),
      (mem_pointsOfDimension C p).mpr (relativeDimension_genericPointOf C p (W j) (hW j)
        (hDim j))⟩ with hπ
  have hKfin : {j : J | y ∈ ((W j).support : Set X)}.Finite :=
    finite_mem_support_of_locallyFinite W hLocal y
  set Ks := hKfin.toFinset
  set F : J → ℤ := fun j ↦ principalDivisorPushforward C p (W j) (hW j) (g j) y
  set G : pointsOfDimension C p (k + 1) → ℤ := fun x ↦
    pointwiseDivisorTerm C p k (pointwiseChainOfFamily C p k W hW hLocal g) x y
  set T : Finset (pointsOfDimension C p (k + 1)) := Ks.image π
  have hold : principalDivisorFamilyCoefficient C p W hW g y = ∑ j ∈ Ks, F j :=
    finsum_eq_sum_of_support_subset F fun j hj ↦
      hKfin.mem_toFinset.mpr
        (support_principalDivisorPushforward_subset C p (W j) (hW j) (g j) hj)
  have hnew : (pointwiseDivisorSum C p k
      (pointwiseChainOfFamily C p k W hW hLocal g)).1 y = ∑ x ∈ T, G x := by
    rw [pointwiseDivisorSum_apply]
    refine finsum_eq_sum_of_support_subset G fun x hx ↦ ?_
    have hax : (pointwiseChainOfFamily C p k W hW hLocal g).1 x ≠ 0 := fun h ↦
      hx (pointwiseDivisorTerm_apply_of_eq_zero C p k _ h y)
    have hy : y ∈ closure ({x.1} : Set X) := of_not_not fun hnot ↦
      hx (pointwiseDivisorTerm_apply_of_notMem_closure C p k _ x hnot)
    have hu : familyResidueFieldUnit W hW g x.1 ≠ 1 := fun h ↦
      hax ((pointwiseChainOfFamily_eq_zero_iff C p k W hW hLocal g x).mpr h)
    obtain ⟨j, hj⟩ := exists_genericPointOf_eq_of_familyResidueFieldUnit_ne_one W hW g hu
    refine Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨j, hKfin.mem_toFinset.mpr ?_,
      Subtype.ext hj⟩)
    exact (mem_support_iff_mem_closure_of_genericPointOf_eq (hW j) hj y).mpr hy
  have hfiber : ∀ x ∈ T, G x = ∑ j ∈ Ks.filter fun j ↦ π j = x, F j := by
    intro x hx
    obtain ⟨j₀, hj₀, hj₀x⟩ := Finset.mem_image.mp hx
    have h₀ : y ∈ closure ({x.1} : Set X) :=
      (mem_support_iff_mem_closure_of_genericPointOf_eq (hW j₀)
        (show genericPointOf (W j₀) (hW j₀) = x.1 from congrArg Subtype.val hj₀x) y).mp
        (hKfin.mem_toFinset.mp hj₀)
    have hfilter : (Ks.filter fun j ↦ π j = x) =
        Ks.filter fun j ↦ genericPointOf (W j) (hW j) = x.1 :=
      Finset.filter_congr fun j _ ↦ by simp only [hπ, Subtype.ext_iff]
    rw [hfilter]
    exact pointwiseDivisorTerm_pointwiseChainOfFamily_eq_sum_filter C p k W hW hLocal g x h₀ Ks
      fun j hj ↦ hKfin.mem_toFinset.mpr hj
  rw [hnew, hold, Finset.sum_congr rfl hfiber]
  exact Finset.sum_fiberwise_of_maps_to (fun j hj ↦ Finset.mem_image_of_mem π hj) F

/-! ### Exactness of the presentation -/

/-- The cycle underlying the divisor of a pointwise Milnor K₁-chain. -/
@[simp]
theorem pointwiseCycleEquiv_symm_pointwiseDivisorDifferential (k : ℤ)
    (a : PointwiseKOneGroup C p k) :
    (pointwiseCycleEquiv C p k).symm (pointwiseDivisorDifferential C p k a) =
      pointwiseDivisorSum C p k a := by
  simp [pointwiseDivisorDifferential]

/-- Half of Stacks 0GU3: the divisor of a pointwise Milnor K₁-chain has vanishing Chow class.
Indeed it is, by construction, the locally finite sum of the pushed-forward principal divisors
of nonzero rational functions on the integral closed subschemes `closure {x}` of
delta-dimension `k + 1`, which is what it means to be rationally equivalent to zero. -/
theorem pointwiseDivisorDifferential_range_le_ker_pointwiseChowClass (k : ℤ) :
    (pointwiseDivisorDifferential C p k).range ≤ (pointwiseChowClass C p k).ker := by
  rintro _ ⟨a, rfl⟩
  rw [pointwiseChowClass_mem_ker_iff, mem_rationalEquivalences,
    pointwiseCycleEquiv_symm_pointwiseDivisorDifferential]
  exact ⟨{x : pointsOfDimension C p (k + 1) // a.1 x ≠ 0},
    fun j ↦ integralComponentAt j.1.1, fun j ↦ isIntegral_integralComponentAt j.1.1,
    fun j ↦ by
      rw [schemeDeltaDimension_integralComponentAt C p]
      exact congrArg _ ((mem_pointsOfDimension C p).mp j.1.2),
    by
      simpa only [coe_support_integralComponentAt] using
        locallyFinite_closure_pointwiseSupport C p k a,
    fun j ↦ pointwiseComponentFunction C p k a j.1,
    pointwiseDivisorSum_spec C p k a⟩

/-- Half of Stacks 0GU3: a pointwise Milnor K₀-chain with vanishing Chow class is a pointwise
divisor. The cycle it names is a locally finite sum of pushed-forward principal divisors of
nonzero rational functions `g j` on integral closed subschemes `W j` of delta-dimension
`k + 1`; the Milnor K₁-chain whose class at a point `x` is the product of the values at `x` of
those `g j` whose `W j` has generic point `x` has that cycle as its divisor. -/
theorem ker_pointwiseChowClass_le_pointwiseDivisorDifferential_range (k : ℤ) :
    (pointwiseChowClass C p k).ker ≤ (pointwiseDivisorDifferential C p k).range := by
  intro b hb
  obtain ⟨J, W, hW, hDim, hLocal, g, hCoeff⟩ :=
    (mem_rationalEquivalences C p k _).mp ((pointwiseChowClass_mem_ker_iff C p k b).mp hb)
  refine ⟨pointwiseChainOfFamily C p k W hW hLocal g, ?_⟩
  refine (pointwiseCycleEquiv C p k).symm.injective ?_
  rw [pointwiseCycleEquiv_symm_pointwiseDivisorDifferential]
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y ↦ ?_)
  rw [pointwiseDivisorSum_pointwiseChainOfFamily C p k W hW hDim hLocal g y]
  exact (hCoeff y).symm

/-- **Stacks 0GU3.** The presentation of the Chow group is exact in the middle: a pointwise
Milnor K₀-chain is a pointwise divisor exactly when the cycle it names is rationally equivalent
to zero. -/
@[stacks 0GU3 "exactness of the presentation"]
theorem pointwiseDivisorDifferential_range_eq_ker_pointwiseChowClass (k : ℤ) :
    (pointwiseDivisorDifferential C p k).range = (pointwiseChowClass C p k).ker :=
  le_antisymm (pointwiseDivisorDifferential_range_le_ker_pointwiseChowClass C p k)
    (ker_pointwiseChowClass_le_pointwiseDivisorDifferential_range C p k)

end Stacks.Chow

end
