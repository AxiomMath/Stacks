module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.MultiplicativeGroupDivisorClass
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointDivisorEpi
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassBijective
public import StacksFrontier.AlgebraicGeometry.Divisors.PrimeDivisorStalk
public import StacksFrontier.AlgebraicGeometry.AmpleDimensionOne.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PicardShrink
public import StacksFrontier.AlgebraicGeometry.Picard.CurveDegree
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorSheafDegree
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AmpleSmoothIrreducible
public import StacksFrontier.AlgebraicGeometry.CurveFiniteMorphism.Basic
public import StacksFrontier.AlgebraicGeometry.CurveLocalRing.ClosedPointDivisor
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CanonicalSectionOrder
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.Local.OrderComparison
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicOrder.Stalk
public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegreeFormula
public import StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward.StalkTransport
public import StacksFrontier.AlgebraicGeometry.Chow.EnvelopeCycleLift
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.Variety.SeparatingPointsTangentVectors.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness

/-!
# The divisor class group of a smooth curve is its Picard group

Let `X` be a smooth curve over an algebraically closed field `k`. The divisor class group
`Stacks.EtaleCohomology.curveClassGroup g = (X_0 →₀ 𝐙)/div(K^*)` of the closed points of `X` is
the Picard group `AlgebraicGeometry.schemePicard X` on which the degree
`AlgebraicGeometry.picardDegree` is defined:

* the prime divisors of a curve are its closed points
  (`Stacks.EtaleCohomology.primeDivisorEquivClosedPoints`), so the Weil divisor class group
  `AlgebraicGeometry.weilDivisorClassGroup X` is `curveClassGroup g`;
* the local rings of a smooth curve are discrete valuation rings or fields, hence unique
  factorization domains, so Tag 0BE9 identifies `Cl(X)` with `Pic(X)`;
* the two models of `Pic(X)` are matched by `Stacks.SheafOfModules.picardGroupShrinkAddEquiv`.

## Main results

* `Stacks.EtaleCohomology.weilDivisorClassGroupAddEquivClosedPointClassGroup`: `Cl(X)` is the
  closed-point class group.
* `Stacks.EtaleCohomology.closedPointClassGroupAddEquivSchemePicard`,
  `Stacks.EtaleCohomology.curveClassGroupAddEquivSchemePicard`: `curveClassGroup g ≃+ Pic(X)`.
* `Stacks.EtaleCohomology.closedPointClassGroupAddEquivSchemePicard_single`: the class of a closed
  point `x` goes to the class of `𝒪_X(x)`, which has degree one when `X` is proper
  (`Stacks.EtaleCohomology.picardDegree_closedPointClassGroupAddEquivSchemePicard_single`).
* `Stacks.EtaleCohomology.sum_closedPointDivisorOfUnit_eq_zero`: a principal divisor on a smooth
  proper curve over an algebraically closed field has degree zero.
* `Stacks.EtaleCohomology.curveClassGroupDegree`, `curveClassGroupDegreeZeroAddEquiv`: the degree
  on `Cl(X)` and `Cl⁰(X) ≃+ Pic⁰(X)` (`AlgebraicGeometry.picardDegreeZero`).

## References

* [Stacks Project, Tag 0BE9](https://stacks.math.columbia.edu/tag/0BE9)
* [Stacks Project, Tag 0B8Y](https://stacks.math.columbia.edu/tag/0B8Y)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

/-! ### Prime divisors of a curve are its closed points -/

section PrimeDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g]

include g in
/-- The generic point of a prime divisor of a curve is a closed point: it has coheight one, so it
is not the generic point of the curve. -/
theorem isClosed_singleton_genericPoint_of_isCurve (Z : PrimeDivisor X) :
    IsClosed ({Z.genericPoint} : Set X) := by
  refine Stacks.AlgebraicGeometry.AmpleDimensionOne.isClosed_singleton_of_ne_genericPoint X
    (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)) fun h => ?_
  have h1 := Z.coheight_genericPoint
  rw [h, show genericPoint X = (⊤ : X) from rfl, Order.coheight_top] at h1
  exact zero_ne_one h1

/-- **The prime divisors of a curve are its closed points**: a prime divisor is determined by its
generic point, the generic points of prime divisors are the points of coheight one, and on a curve
these are the closed points. -/
def primeDivisorEquivClosedPoints : PrimeDivisor X ≃ closedPoints X where
  toFun Z := ⟨Z.genericPoint, isClosed_singleton_genericPoint_of_isCurve g Z⟩
  invFun x := PrimeDivisor.ofCoheightOne x.1
    (IsCurve.coheight_eq_one (f := g) (ne_genericPoint_of_mem_closedPoints_of_isCurve g x))
  left_inv Z := PrimeDivisor.genericPoint_injective (PrimeDivisor.genericPoint_ofCoheightOne _ _)
  right_inv x := Subtype.ext (by exact PrimeDivisor.genericPoint_ofCoheightOne _ _)

/-- The closed point corresponding to a prime divisor is its generic point. -/
@[simp]
theorem primeDivisorEquivClosedPoints_apply_coe (Z : PrimeDivisor X) :
    (primeDivisorEquivClosedPoints g Z : X) = Z.genericPoint :=
  rfl

/-- The generic point of the prime divisor corresponding to a closed point `x` is `x`. -/
@[simp]
theorem genericPoint_primeDivisorEquivClosedPoints_symm (x : closedPoints X) :
    ((primeDivisorEquivClosedPoints g).symm x).genericPoint = x.1 :=
  PrimeDivisor.genericPoint_ofCoheightOne x.1
    (IsCurve.coheight_eq_one (f := g) (ne_genericPoint_of_mem_closedPoints_of_isCurve g x))

end PrimeDivisor

/-! ### The Weil divisor class group of a curve -/

section WeilDivisor

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g]
  [IsLocallyNoetherian X] [AlgebraicGeometry.IsNoetherian X]

/-- **The Weil divisors of a curve are the divisors supported on its closed points.** -/
def weilDivisorAddEquivClosedPointDivisor : WeilDivisor X ≃+ (closedPoints X →₀ ℤ) :=
  weilDivisorEquivFinsupp.trans (Finsupp.domCongr (primeDivisorEquivClosedPoints g))

omit [IsLocallyNoetherian X] in
/-- The coefficient of the closed-point divisor of a Weil divisor `D` at a closed point `x` is the
coefficient of `D` at the prime divisor corresponding to `x`. -/
@[simp]
theorem weilDivisorAddEquivClosedPointDivisor_apply (D : WeilDivisor X) (x : closedPoints X) :
    weilDivisorAddEquivClosedPointDivisor g D x =
      D.val ((primeDivisorEquivClosedPoints g).symm x) :=
  rfl

/-- The units of the ring of rational functions are the units of the function field. -/
def rationalFunctionsUnitsMulEquiv (X : Scheme.{u}) [AlgebraicGeometry.IsIntegral X] :
    (Stacks.Chow.rationalFunctions X)ˣ ≃* (X.functionField)ˣ :=
  Units.mapEquiv (Stacks.Chow.rationalFunctionsEquivFunctionField X).val.toMulEquiv

/-- **Principal Weil divisors are the principal closed-point divisors.** -/
theorem weilDivisorAddEquivClosedPointDivisor_principalDivisor
    (f : (Stacks.Chow.rationalFunctions X)ˣ) :
    weilDivisorAddEquivClosedPointDivisor g (principalDivisor X f) =
      closedPointDivisorOfUnit X (Additive.ofMul (rationalFunctionsUnitsMulEquiv X f)) := by
  ext x
  rw [weilDivisorAddEquivClosedPointDivisor_apply, principalDivisor_apply,
    closedPointDivisorOfUnit_apply, genericPoint_primeDivisorEquivClosedPoints_symm]
  rfl

/-- The image of the subgroup of principal Weil divisors under
`weilDivisorAddEquivClosedPointDivisor` is the subgroup of principal closed-point divisors. -/
theorem map_principalWeilDivisors :
    (principalWeilDivisors X).map (weilDivisorAddEquivClosedPointDivisor g).toAddMonoidHom =
      (closedPointDivisorOfUnit X).range := by
  ext d
  constructor
  · rintro ⟨_, ⟨f, rfl⟩, rfl⟩
    exact ⟨_, (weilDivisorAddEquivClosedPointDivisor_principalDivisor g f).symm⟩
  · rintro ⟨f, rfl⟩
    refine ⟨principalDivisor X ((rationalFunctionsUnitsMulEquiv X).symm (Additive.toMul f)),
      ⟨_, rfl⟩, ?_⟩
    change weilDivisorAddEquivClosedPointDivisor g _ = _
    rw [weilDivisorAddEquivClosedPointDivisor_principalDivisor, MulEquiv.apply_symm_apply]
    rfl

/-- **The Weil divisor class group of a curve is its closed-point class group.** -/
def weilDivisorClassGroupAddEquivClosedPointClassGroup :
    weilDivisorClassGroup X ≃+ closedPointClassGroup X :=
  QuotientAddGroup.congr _ _ (weilDivisorAddEquivClosedPointDivisor g) (map_principalWeilDivisors g)

/-- The class of a Weil divisor `D` maps to the class of the corresponding closed-point divisor. -/
theorem weilDivisorClassGroupAddEquivClosedPointClassGroup_mk (D : WeilDivisor X) :
    weilDivisorClassGroupAddEquivClosedPointClassGroup g (D : weilDivisorClassGroup X) =
      (QuotientAddGroup.mk (weilDivisorAddEquivClosedPointDivisor g D) :
        closedPointClassGroup X) :=
  rfl

end WeilDivisor

/-! ### `Cl(X) = Pic(X)` for a smooth curve -/

section Picard

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup
  AlgebraicGeometry.schemePicardGroupAddCommGroup

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]

variable [IsLocallyNoetherian X] [AlgebraicGeometry.IsNoetherian X]

/-- **The closed-point class group of a smooth curve is its Picard group**: Tag 0BE9, the prime
divisors being the closed points. -/
def closedPointClassGroupAddEquivSchemePicard : closedPointClassGroup X ≃+ schemePicard X :=
  (weilDivisorClassGroupAddEquivClosedPointClassGroup g).symm.trans
    ((picardEquivWeilDivisorClassGroupOfForallUniqueFactorizationMonoid X
      (AlgebraicGeometry.uniqueFactorizationMonoid_stalk_of_smooth g)).symm.trans
      (Stacks.SheafOfModules.picardGroupShrinkAddEquiv X.sheaf.obj X.ringCatSheaf.property))

end Picard

/-! ### The class of a closed point -/

section ClosedPoint

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup
  AlgebraicGeometry.schemePicardGroupAddCommGroup

/-- The abelian group structure of the small model of `Pic(X)` at the index `X.sheaf.obj`. -/
local instance schemeSheafPicardAddCommGroup (X : Scheme.{u}) :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj X.ringCatSheaf.property) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup X.sheaf.obj X.ringCatSheaf.property

variable {k : Type u} [Field k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k)) [IsCurve k g] [Smooth g]

include g in
/-- The reduced closed subscheme supported on a closed point of a smooth curve, as an effective
Cartier divisor. -/
theorem isEffectiveCartierDivisor_closedPoint (x : closedPoints X) :
    Stacks.Divisors.IsEffectiveCartierDivisor
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X))) :=
  IsCurve.isEffectiveCartierDivisor_vanishingIdeal_closure_singleton k g x.2

variable [IsLocallyNoetherian X]

open scoped Classical in
include g in
/-- **The local equation of a closed point has order one there and zero elsewhere.** If `c`
generates the ideal that the reduced point `x` induces in the local ring at a point `z` of
coheight one, then `ord_z(c)` is `1` for `z = x` (a generator of the maximal ideal of the
discrete valuation ring `𝒪_{X,x}` is a uniformizer) and `0` otherwise (`c` is a unit). -/
theorem ord_of_stalk_vanishingIdeal_closure_singleton_eq_span (x : closedPoints X) {z : X}
    (hz : Order.coheight z = 1) (c : X.presheaf.stalk z)
    (hc : IdealSheafData.stalk
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X))) z =
        Ideal.span {c}) :
    X.ord (algebraMap (X.presheaf.stalk z) X.functionField c) z = if z = x.1 then 1 else 0 := by
  obtain ⟨x, hx⟩ := x
  change IsClosed ({x} : Set X) at hx
  change _ = if z = x then 1 else 0
  split_ifs with h
  · subst h
    have hdvr : IsDiscreteValuationRing (X.presheaf.stalk z) :=
      IsCurve.isDiscreteValuationRing_stalk_of_isClosed k g hx
    have hirr : Irreducible c := (IsDiscreteValuationRing.irreducible_iff_uniformizer c).2
      ((Stacks.Divisors.stalk_vanishingIdeal_closure_singleton z).symm.trans hc)
    exact_mod_cast Stacks.Chow.ord_algebraMap_eq_ringOrd hz hirr.ne_zero (n := 1)
      (Ring.ord_of_irreducible hirr)
  · have hnot : z ∉ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).support := by
      intro hmem
      have hmem' : z ∈ ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set X))).support : Set X) := hmem
      rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure,
        hx.closure_eq, Set.mem_singleton_iff] at hmem'
      exact h hmem'
    have htop := (IdealSheafData.stalk_eq_top_iff_notMem_support _ z).2 hnot
    rw [hc, Ideal.span_singleton_eq_top] at htop
    exact Scheme.ord_algebraMap_of_isUnit hz htop

/-- **The Weil divisor class of `𝒪_X(x)` is the class of the prime divisor `x`.** -/
theorem weilDivisorClassOfInvertibleSheaf_closedPoint [AlgebraicGeometry.IsNoetherian X]
    (x : closedPoints X) :
    haveI := isEffectiveCartierDivisor_closedPoint g x
    weilDivisorClassOfInvertibleSheaf X (Stacks.Divisors.modulesInvertibleSheaf
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X)))) =
      (((weilDivisorAddEquivClosedPointDivisor g).symm (Finsupp.single x 1) : WeilDivisor X) :
        weilDivisorClassGroup X) := by
  classical
  have := isEffectiveCartierDivisor_closedPoint g x
  refine weilDivisorClassOfInvertibleSheaf_eq_of_forall_ord _ _ fun Z c hc => ?_
  rw [ord_of_stalk_vanishingIdeal_closure_singleton_eq_span g x Z.coheight_genericPoint c hc]
  have hval : ((weilDivisorAddEquivClosedPointDivisor g).symm (Finsupp.single x 1)).val Z =
      Finsupp.single x (1 : ℤ) (primeDivisorEquivClosedPoints g Z) := by
    have h := weilDivisorAddEquivClosedPointDivisor_apply g
      ((weilDivisorAddEquivClosedPointDivisor g).symm (Finsupp.single x 1))
      (primeDivisorEquivClosedPoints g Z)
    rw [AddEquiv.apply_symm_apply, Equiv.symm_apply_apply] at h
    exact h.symm
  rw [hval, Finsupp.single_apply]
  by_cases h : Z.genericPoint = x.1
  · rw [ite_eq_left h, ite_eq_left (Subtype.ext h.symm)]
  · rw [ite_eq_right h, ite_eq_right fun h' => h (congrArg Subtype.val h').symm]

/-- **Under `Cl(X) ≅ Pic(X)` the class of a closed point `x` is the class of `𝒪_X(x)`.** -/
theorem closedPointClassGroupAddEquivSchemePicard_single [AlgebraicGeometry.IsNoetherian X]
    (x : closedPoints X) :
    closedPointClassGroupAddEquivSchemePicard g
        (QuotientAddGroup.mk (Finsupp.single x 1) : closedPointClassGroup X) =
      haveI := isEffectiveCartierDivisor_closedPoint g x
      divisorSchemePicardClass
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X))) := by
  have := isEffectiveCartierDivisor_closedPoint g x
  have h1 : (Stacks.SheafOfModules.picardGroupShrinkAddEquiv X.sheaf.obj
      X.ringCatSheaf.property).symm (divisorSchemePicardClass
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X)))) =
      Stacks.SheafOfModules.picardClass X.sheaf.obj X.ringCatSheaf.property
        (Stacks.Divisors.divisorSheaf
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X))))
        (stacksIsInvertible_divisorSheaf _) :=
    (AddEquiv.symm_apply_eq _).2 rfl
  have h2 : (closedPointClassGroupAddEquivSchemePicard g).symm (divisorSchemePicardClass
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X)))) =
      (QuotientAddGroup.mk (Finsupp.single x 1) : closedPointClassGroup X) := by
    change weilDivisorClassGroupAddEquivClosedPointClassGroup g
      (picardToWeilDivisorClassGroup X ((Stacks.SheafOfModules.picardGroupShrinkAddEquiv
        X.sheaf.obj X.ringCatSheaf.property).symm (divisorSchemePicardClass
          (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X)))))) = _
    rw [h1]
    change weilDivisorClassGroupAddEquivClosedPointClassGroup g
      (weilDivisorClassOfPicardClass X _) = _
    refine (congrArg (weilDivisorClassGroupAddEquivClosedPointClassGroup g)
      ((@weilDivisorClassOfPicardClass_picardClass X _ _ _
          (stacksIsInvertible_divisorSheaf _)).trans
        (weilDivisorClassOfInvertibleSheaf_closedPoint g x))).trans ?_
    rw [weilDivisorClassGroupAddEquivClosedPointClassGroup_mk, AddEquiv.apply_symm_apply]
  exact ((AddEquiv.symm_apply_eq _).1 h2).symm

omit [IsCurve k g] [IsLocallyNoetherian X] in
/-- **The reduced closed point of a curve over an algebraically closed field has degree one**: its
ring of functions is the residue field, which is `k`. -/
theorem finrank_globalSections_closedPoint [IsAlgClosed k] (x : closedPoints X) :
    letI : Algebra k Γ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x.1} : Set X))).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x.1} : Set X))).subschemeι ≫ g).appTop).hom.toAlgebra
    Module.finrank k Γ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x.1} : Set X))).subscheme, ⊤) = 1 := by
  set D := Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X))
  have : AlgebraicGeometry.IsIntegral D.subscheme :=
    Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure x.1
  have hrange : ∀ a : D.subscheme, D.subschemeι a = x.1 := fun a => by
    have ha : D.subschemeι a ∈ Set.range D.subschemeι := ⟨a, rfl⟩
    rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal,
      Closeds.coe_closure, (x.2 : IsClosed ({x.1} : Set X)).closure_eq] at ha
    exact ha
  have : Subsingleton D.subscheme := ⟨fun a b =>
    D.subschemeι.isClosedEmbedding.injective ((hrange a).trans (hrange b).symm)⟩
  rw [← Stacks.Chow.residueDegree_eq_finrank_globalSections k (D.subschemeι ≫ g)
    (genericPoint D.subscheme)]
  exact Stacks.Chow.residueDegree_eq_one_of_residueFieldMap_isIso _ _
    (AlgebraicGeometry.isIso_residueFieldMap_of_isClosed (D.subschemeι ≫ g) (𝟙 _) _
      (Set.Subsingleton.isClosed Set.subsingleton_of_subsingleton))

/-- **The class of a closed point of a smooth proper curve over an algebraically closed field has
degree one.** -/
theorem picardDegree_closedPointClassGroupAddEquivSchemePicard_single [IsAlgClosed k]
    [IsProper g] [AlgebraicGeometry.IsNoetherian X] (hdim : topologicalKrullDim X ≤ 1)
    (x : closedPoints X) :
    picardDegree k g hdim (closedPointClassGroupAddEquivSchemePicard g
        (QuotientAddGroup.mk (Finsupp.single x 1) : closedPointClassGroup X)) = 1 := by
  have := isEffectiveCartierDivisor_closedPoint g x
  rw [closedPointClassGroupAddEquivSchemePicard_single,
    picardDegree_divisorSchemePicardClass k g hdim, finrank_globalSections_closedPoint g x,
    Nat.cast_one]

end ClosedPoint

/-! ### The degree -/

section Degree

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g] [IsProper g] [IsLocallyNoetherian X] [AlgebraicGeometry.IsNoetherian X]

/-- **The degree of the line bundle of a divisor `D = ∑ n_x [x]` is `∑ n_x`**, on a smooth proper
curve over an algebraically closed field. -/
theorem picardDegree_closedPointClassGroupAddEquivSchemePicard_mk
    (hdim : topologicalKrullDim X ≤ 1) (d : closedPoints X →₀ ℤ) :
    picardDegree k g hdim (closedPointClassGroupAddEquivSchemePicard g
        (QuotientAddGroup.mk d : closedPointClassGroup X)) = d.sum fun _ n => n := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d d' hd hd' =>
    rw [QuotientAddGroup.mk_add, map_add, map_add, hd, hd', Finsupp.sum_add_index'] <;> simp
  | single x n =>
    have h : (QuotientAddGroup.mk (Finsupp.single x n) : closedPointClassGroup X) =
        n • (QuotientAddGroup.mk (Finsupp.single x 1) : closedPointClassGroup X) := by
      rw [← QuotientAddGroup.mk_zsmul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [h, map_zsmul, map_zsmul,
      picardDegree_closedPointClassGroupAddEquivSchemePicard_single g hdim x,
      Finsupp.sum_single_index rfl, smul_eq_mul, mul_one]

include g in
/-- **A principal divisor on a smooth proper curve over an algebraically closed field has degree
zero**: its line bundle is trivial. -/
theorem sum_closedPointDivisorOfUnit_eq_zero (f : Additive (X.functionField)ˣ) :
    ((closedPointDivisorOfUnit X f).sum fun _ n => n) = 0 := by
  have hdim : topologicalKrullDim X ≤ 1 := (IsCurve.topologicalKrullDim_eq_one (k := k) (f := g)).le
  rw [← picardDegree_closedPointClassGroupAddEquivSchemePicard_mk g hdim,
    (QuotientAddGroup.eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨f, rfl⟩), map_zero,
    map_zero]

/-- **The degree on the divisor class group** `∑ n_x [x] ↦ ∑ n_x` of a smooth proper curve over an
algebraically closed field; it is well defined by
`Stacks.EtaleCohomology.sum_closedPointDivisorOfUnit_eq_zero`. -/
def closedPointClassGroupDegree : closedPointClassGroup X →+ ℤ :=
  QuotientAddGroup.lift _ (Finsupp.liftAddHom fun _ => AddMonoidHom.id ℤ) (by
    rintro _ ⟨f, rfl⟩
    rw [AddMonoidHom.mem_ker, Finsupp.liftAddHom_apply]
    exact sum_closedPointDivisorOfUnit_eq_zero g f)

/-- The degree of the class of a divisor `∑ n_x [x]` is `∑ n_x`. -/
@[simp]
theorem closedPointClassGroupDegree_mk (d : closedPoints X →₀ ℤ) :
    closedPointClassGroupDegree g (QuotientAddGroup.mk d : closedPointClassGroup X) =
      d.sum fun _ n => n :=
  Finsupp.liftAddHom_apply _ _

/-- **`Cl(X) ≅ Pic(X)` preserves degrees.** -/
theorem picardDegree_closedPointClassGroupAddEquivSchemePicard
    (hdim : topologicalKrullDim X ≤ 1) (c : closedPointClassGroup X) :
    picardDegree k g hdim (closedPointClassGroupAddEquivSchemePicard g c) =
      closedPointClassGroupDegree g c := by
  induction c using QuotientAddGroup.induction_on with
  | H d => rw [picardDegree_closedPointClassGroupAddEquivSchemePicard_mk,
      closedPointClassGroupDegree_mk]

/-- **`Cl⁰(X) ≅ Pic⁰(X)`**: the degree-zero divisor classes of a smooth proper curve over an
algebraically closed field are the degree-zero line bundles. -/
def closedPointClassGroupDegreeZeroAddEquiv (hdim : topologicalKrullDim X ≤ 1) :
    (closedPointClassGroupDegree g).ker ≃+ picardDegreeZero k g hdim where
  toFun c := ⟨closedPointClassGroupAddEquivSchemePicard g c.1, by
    rw [mem_picardDegreeZero_iff, picardDegree_closedPointClassGroupAddEquivSchemePicard]
    exact c.2⟩
  invFun y := ⟨(closedPointClassGroupAddEquivSchemePicard g).symm y.1, by
    rw [AddMonoidHom.mem_ker, ← picardDegree_closedPointClassGroupAddEquivSchemePicard g hdim,
      AddEquiv.apply_symm_apply]
    exact y.2⟩
  left_inv c := Subtype.ext (AddEquiv.symm_apply_apply _ _)
  right_inv y := Subtype.ext (AddEquiv.apply_symm_apply _ _)
  map_add' c c' := Subtype.ext (map_add (closedPointClassGroupAddEquivSchemePicard g) c.1 c'.1)

/-- The line bundle class attached to a degree-zero divisor class `c` is the image of `c` under
`closedPointClassGroupAddEquivSchemePicard`. -/
@[simp]
theorem coe_closedPointClassGroupDegreeZeroAddEquiv (hdim : topologicalKrullDim X ≤ 1)
    (c : (closedPointClassGroupDegree g).ker) :
    (closedPointClassGroupDegreeZeroAddEquiv g hdim c : schemePicard X) =
      closedPointClassGroupAddEquivSchemePicard g c.1 :=
  rfl

end Degree

/-! ### In the spelling `curveClassGroup` -/

section Curve

attribute [local instance] AlgebraicGeometry.SmallEtale.zariskiPicardAddCommGroup

variable {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}} (g : X ⟶ Spec (.of k))
  [IsCurve k g] [Smooth g]

/-- **The divisor class group of a smooth curve over an algebraically closed field is its Picard
group** (Tag 0BE9). -/
def curveClassGroupAddEquivSchemePicard : curveClassGroup g ≃+ schemePicard X :=
  haveI := isLocallyNoetherian_of_isCurve g
  haveI := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  closedPointClassGroupAddEquivSchemePicard g

omit [IsAlgClosed k] in
/-- Under `Cl(X) ≅ Pic(X)` the class of a closed point `x` is the class of `𝒪_X(x)`. -/
theorem curveClassGroupAddEquivSchemePicard_single (x : closedPoints X) :
    curveClassGroupAddEquivSchemePicard g
        (QuotientAddGroup.mk (Finsupp.single x 1) : curveClassGroup g) =
      haveI := isEffectiveCartierDivisor_closedPoint g x
      divisorSchemePicardClass
        (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({x.1} : Set X))) :=
  have := isLocallyNoetherian_of_isCurve g
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  closedPointClassGroupAddEquivSchemePicard_single g x

variable [IsProper g]

/-- The class of a closed point of a smooth proper curve over an algebraically closed field has
degree one. -/
theorem picardDegree_curveClassGroupAddEquivSchemePicard_single
    (hdim : topologicalKrullDim X ≤ 1) (x : closedPoints X) :
    picardDegree k g hdim (curveClassGroupAddEquivSchemePicard g
        (QuotientAddGroup.mk (Finsupp.single x 1) : curveClassGroup g)) = 1 :=
  have := isLocallyNoetherian_of_isCurve g
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  picardDegree_closedPointClassGroupAddEquivSchemePicard_single g hdim x

/-- **The degree on the divisor class group** of a smooth proper curve over an algebraically
closed field, `∑ n_x [x] ↦ ∑ n_x`. -/
def curveClassGroupDegree : curveClassGroup g →+ ℤ :=
  haveI := isLocallyNoetherian_of_isCurve g
  haveI := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  closedPointClassGroupDegree g

/-- The degree of the class of a divisor `∑ n_x [x]` is `∑ n_x`. -/
@[simp]
theorem curveClassGroupDegree_mk (d : closedPoints X →₀ ℤ) :
    curveClassGroupDegree g (QuotientAddGroup.mk d : curveClassGroup g) = d.sum fun _ n => n :=
  have := isLocallyNoetherian_of_isCurve g
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  closedPointClassGroupDegree_mk g d

/-- `Cl(X) ≅ Pic(X)` preserves degrees. -/
theorem picardDegree_curveClassGroupAddEquivSchemePicard (hdim : topologicalKrullDim X ≤ 1)
    (c : curveClassGroup g) :
    picardDegree k g hdim (curveClassGroupAddEquivSchemePicard g c) = curveClassGroupDegree g c :=
  have := isLocallyNoetherian_of_isCurve g
  have := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  picardDegree_closedPointClassGroupAddEquivSchemePicard g hdim c

/-- **`Cl⁰(X) ≅ Pic⁰(X)`** for a smooth proper curve over an algebraically closed field. -/
def curveClassGroupDegreeZeroAddEquiv (hdim : topologicalKrullDim X ≤ 1) :
    (curveClassGroupDegree g).ker ≃+ picardDegreeZero k g hdim :=
  haveI := isLocallyNoetherian_of_isCurve g
  haveI := Stacks.ProjectiveSpaceSections.isNoetherian_of_isCurve g
  closedPointClassGroupDegreeZeroAddEquiv g hdim

/-- The line bundle class attached to a degree-zero divisor class `c` is the image of `c` under
`curveClassGroupAddEquivSchemePicard`. -/
@[simp]
theorem coe_curveClassGroupDegreeZeroAddEquiv (hdim : topologicalKrullDim X ≤ 1)
    (c : (curveClassGroupDegree g).ker) :
    (curveClassGroupDegreeZeroAddEquiv g hdim c : schemePicard X) =
      curveClassGroupAddEquivSchemePicard g c.1 :=
  rfl

end Curve

end Stacks.EtaleCohomology

end
