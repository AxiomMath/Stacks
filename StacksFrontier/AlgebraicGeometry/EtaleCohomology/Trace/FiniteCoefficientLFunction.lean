module

public import StacksFrontier.Algebra.Module.Projective.Determinant.CharSeries
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ConstructibleFlatLFunction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The L-function of a constructible flat module over an arbitrary finite coefficient ring

Let `X` be a scheme of finite type over a finite field `k` and let `Λ` be a commutative ring (for
instance a finite ring of order prime to the characteristic of `k`). The L-function of a
constructible flat `Λ`-module `ℱ` on `X_étale` is the Euler product

`L(X, ℱ) = ∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄}) ⁻¹ ∈ Λ⟦T⟧`.

The stalks of `ℱ` are finite projective `Λ`-modules. Over a non-local ring such as `ℤ/6ℤ` they
need not be free, and Mathlib's `LinearMap.det` would take its junk value on them, so the local
factor here is the projective determinant `ProjectiveDeterminant.charSeries` of the geometric
Frobenius. When `Λ` is local this is the L-function `lFunctionOfConstructibleFlat`
(`lFunctionOfFiniteProjectiveStalks_eq_lFunctionOfConstructibleFlat`).

## Main definitions

* `Stacks.EtaleCohomology.finiteProjectiveStalksEulerSystem`: the local factors at the closed
  points, as an Euler system.
* `Stacks.EtaleCohomology.lFunctionOfFiniteProjectiveStalks`: their Euler product, for a sheaf
  with finite projective stalks.
* `Stacks.EtaleCohomology.constructibleFlatLFunction`: the L-function of a constructible flat
  `Λ`-module, for an arbitrary commutative coefficient ring.

## Main results

* `Stacks.EtaleCohomology.coeff_constructibleFlatLFunction_eq`: the product converges.
* `Stacks.EtaleCohomology.isUnit_constructibleFlatLFunction`: the L-function is a unit.
* `Stacks.EtaleCohomology.constructibleFlatLFunction_eq_lFunctionOfConstructibleFlat`: over a
  local ring it is `Stacks.EtaleCohomology.lFunctionOfConstructibleFlat`.

## References

* [Stacks Project, Tag 03UV](https://stacks.math.columbia.edu/tag/03UV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Frobenius

universe u w r

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))
  {k : Type u} [Field k] [Finite k] (f : X.obj ⟶ Spec (.of k)) [LocallyOfFiniteType f]

/-- The geometric Frobenius at a closed point of a scheme of finite type over a finite field, as an
endomorphism of the stalk there. -/
@[sga "4½ Rapport 1.5"]
public abbrev closedPointFrobenius (x : closedPoints X.obj) :
    ↥(frobeniusStalkModule B X Λ F x.1) →ₗ[Λ] ↥(frobeniusStalkModule B X Λ F x.1) :=
  haveI := finite_residueField f x.1 x.2
  (frobeniusStalk (ModuleCat.{w} Λ) X.obj x.1
    ((SmallEtale.sheafEquiv B X.obj X.property (ModuleCat.{w} Λ)).functor.obj F)).hom

variable
  (hfin : ∀ s : GeometricPoint X.obj, Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj F))
  (hproj : ∀ s : GeometricPoint X.obj,
    Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F))

/-- The stalk of `F` on the small étale site is finite projective if the étale stalk is. -/
private theorem finite_projective_frobeniusStalkModule (x : X.obj)
    (hfin : Module.Finite Λ ((etaleModuleStalkFunctor B X Λ (geometricPointAt X.obj x)).obj F))
    (hproj :
      Module.Projective Λ ((etaleModuleStalkFunctor B X Λ (geometricPointAt X.obj x)).obj F)) :
    Module.Finite Λ (frobeniusStalkModule B X Λ F x) ∧
      Module.Projective Λ (frobeniusStalkModule B X Λ F x) :=
  ⟨finite_sheafFiber_sheafEquiv B X Λ _ F hfin, projective_sheafFiber_sheafEquiv B X Λ F _ hproj⟩

/-- The local factor `det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄})` at a closed point, for a sheaf with
finite projective stalks. -/
public def finiteProjectiveLocalCharSeries (x : closedPoints X.obj) : PowerSeries Λ :=
  haveI := finite_sheafFiber_sheafEquiv B X Λ (geometricPointAt X.obj x.1) F (hfin _)
  haveI := projective_sheafFiber_sheafEquiv B X Λ F (geometricPointAt X.obj x.1) (hproj _)
  ProjectiveDeterminant.charSeries (closedPointFrobenius B X Λ F f x) (residueDegree f x.1)

/-- The local Euler factor `det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄}) ⁻¹` at a closed point. -/
public def finiteProjectiveLocalFactor (x : closedPoints X.obj) : PowerSeries Λ :=
  PowerSeries.invOfUnit (finiteProjectiveLocalCharSeries B X Λ F f hfin hproj x) 1

/-- The product of `det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄})` and the local Euler factor at `x` is
`1`. -/
public theorem finiteProjectiveLocalCharSeries_mul_localFactor (x : closedPoints X.obj) :
    finiteProjectiveLocalCharSeries B X Λ F f hfin hproj x *
      finiteProjectiveLocalFactor B X Λ F f hfin hproj x = 1 := by
  obtain ⟨_, _⟩ := finite_projective_frobeniusStalkModule B X Λ F x.1 (hfin _) (hproj _)
  refine PowerSeries.mul_invOfUnit _ _ ?_
  rw [finiteProjectiveLocalCharSeries, ProjectiveDeterminant.constantCoeff_charSeries _
    (residueDegree_pos f x.1 x.2).ne']
  simp

/-- The local Euler factor is congruent to `1` modulo `T ^ (deg x)`. -/
public theorem X_pow_dvd_finiteProjectiveLocalFactor_sub_one (x : closedPoints X.obj) :
    (PowerSeries.X : PowerSeries Λ) ^ residueDegree f x.1 ∣
      finiteProjectiveLocalFactor B X Λ F f hfin hproj x - 1 := by
  obtain ⟨_, _⟩ := finite_projective_frobeniusStalkModule B X Λ F x.1 (hfin _) (hproj _)
  have hdvd := ProjectiveDeterminant.X_pow_dvd_charSeries_sub_one
    (closedPointFrobenius B X Λ F f x) (residueDegree f x.1)
  have : finiteProjectiveLocalFactor B X Λ F f hfin hproj x - 1 =
      -((finiteProjectiveLocalCharSeries B X Λ F f hfin hproj x - 1) *
        finiteProjectiveLocalFactor B X Λ F f hfin hproj x) := by
    linear_combination finiteProjectiveLocalCharSeries_mul_localFactor B X Λ F f hfin hproj x
  rw [this]
  exact (hdvd.mul_right _).neg_right

/-- The local Euler factors of a sheaf with finite projective stalks at the closed points of a
scheme of finite type over a finite field, as an Euler system graded by the residue degree. -/
@[sga "4½ Rapport 1.6" "special case"]
public def finiteProjectiveStalksEulerSystem [QuasiCompact f] :
    EulerSystem Λ (closedPoints X.obj) where
  factor := finiteProjectiveLocalFactor B X Λ F f hfin hproj
  deg := fun x => residueDegree f x.1
  dvd_factor_sub_one := X_pow_dvd_finiteProjectiveLocalFactor_sub_one B X Λ F f hfin hproj
  finite_degLE := finite_setOf_closedPoints_residueDegree_le f

/-- The Euler product `∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄}) ⁻¹` of a sheaf with finite
projective stalks. -/
public def lFunctionOfFiniteProjectiveStalks [QuasiCompact f] : PowerSeries Λ :=
  (finiteProjectiveStalksEulerSystem B X Λ F f hfin hproj).eulerProduct

/-- The Euler product of a sheaf with finite projective stalks is a unit of `Λ⟦T⟧`. -/
public theorem isUnit_lFunctionOfFiniteProjectiveStalks [QuasiCompact f] :
    IsUnit (lFunctionOfFiniteProjectiveStalks B X Λ F f hfin hproj) :=
  EulerSystem.isUnit_eulerProduct _ fun x => residueDegree_pos f x.1 x.2

/-! ### Constructible flat sheaves -/

variable [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]

/-- The L-function `L(X, ℱ) = ∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄}) ⁻¹ ∈ Λ⟦T⟧` of a
constructible flat `Λ`-module on `X_étale`, for a scheme of finite type over a finite field and an
arbitrary commutative coefficient ring `Λ`, in particular any finite ring. Its local factors are
the projective determinants of the geometric Frobenius on the finite projective stalks. -/
@[stacks 03UV "the definition of L(X, F) for a constructible flat Λ-module F over an arbitrary \
finite (indeed commutative) coefficient ring Λ, not necessarily local: the local factors are the \
projective determinants of the geometric Frobenius on the finite projective stalks",
  sga "4½ Rapport 1.6" "partial"]
public def constructibleFlatLFunction [QuasiCompact f]
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) : PowerSeries Λ :=
  lFunctionOfFiniteProjectiveStalks B X Λ F f
    (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)
    (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)

/-- **The defining product converges.** The coefficient of `T ^ j` of `L(X, ℱ)` is that of the
product of the local factors over any finite set of closed points containing those of degree at
most `j`. -/
public theorem coeff_constructibleFlatLFunction_eq [QuasiCompact f]
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) {j : ℕ} {t : Finset (closedPoints X.obj)}
    (ht : ∀ x : closedPoints X.obj, residueDegree f x.1 ≤ j → x ∈ t) :
    PowerSeries.coeff j (constructibleFlatLFunction B X Λ F f hF) =
      PowerSeries.coeff j (∏ x ∈ t, finiteProjectiveLocalFactor B X Λ F f
        (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)
        (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF) x) :=
  EulerSystem.coeff_eulerProduct_eq _ fun x hx =>
    ht x ((EulerSystem.mem_support _).1 hx)

/-- The L-function of a constructible flat sheaf is a unit of `Λ⟦T⟧`. -/
public theorem isUnit_constructibleFlatLFunction [QuasiCompact f]
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    IsUnit (constructibleFlatLFunction B X Λ F f hF) :=
  isUnit_lFunctionOfFiniteProjectiveStalks _ _ _ _ _ _ _

/-- **Over a local ring the two L-functions agree.** For a local coefficient ring the stalks are
free, the projective determinant is the usual determinant, and `constructibleFlatLFunction` is
`lFunctionOfConstructibleFlat`. -/
public theorem constructibleFlatLFunction_eq_lFunctionOfConstructibleFlat [IsLocalRing Λ]
    [QuasiCompact f] (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    constructibleFlatLFunction B X Λ F f hF = lFunctionOfConstructibleFlat B X Λ F f hF := by
  ext j
  rw [lFunctionOfConstructibleFlat, FrobeniusMatrices.coeff_lFunction,
    constructibleFlatLFunction, lFunctionOfFiniteProjectiveStalks,
    EulerSystem.coeff_eulerProduct_eq _ (t := (frobeniusMatricesOfConstructibleFlat B X Λ F f
      hF).eulerSystem.support j) (fun x hx => by
        rw [EulerSystem.mem_support] at hx ⊢; exact hx)]
  congr 1
  refine Finset.prod_congr rfl fun x _ => ?_
  rw [charPowerSeries_frobeniusStalkEnd_eq_localFactor]
  change PowerSeries.invOfUnit _ 1 = PowerSeries.invOfUnit _ 1
  congr 1
  obtain ⟨_, _⟩ := finite_projective_frobeniusStalkModule B X Λ F x.1
    (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF _)
    (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF _)
  have : Module.Free Λ ↥(frobeniusStalkModule B X Λ F x.1) := Module.free_of_flat_of_isLocalRing
  rw [finiteProjectiveLocalCharSeries, ProjectiveDeterminant.charSeries_eq_linearMap_det]
  rfl

end Stacks.EtaleCohomology

end
