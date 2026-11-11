module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ConstructibleFlat
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SheafFrobeniusMatrices

/-!
# The L-function of a constructible flat module on the étale site

Let `X` be a scheme locally of finite type over a finite field `k` and let `Λ` be a local
coefficient ring (for an arbitrary coefficient ring see
`Stacks.EtaleCohomology.constructibleFlatLFunction`). The L-function of a constructible flat
`Λ`-module `ℱ` on `X_étale` is the Euler product

`L(X, ℱ) = ∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄}) ⁻¹ ∈ Λ⟦T⟧`

over the closed points of `X`, where `deg x = [κ(x) : k]` and `π_x^*` is the geometric Frobenius
acting on the stalk of `ℱ` at a geometric point over `x`.

Every ingredient of the product is read off `ℱ`. A constructible flat sheaf is, on each stratum of
a constructible stratification of an affine open, locally constant with finite projective values,
and a stalk is one of those values; so the stalks are finite projective `Λ`-modules. Over a local
ring a finite projective module is free, so the geometric Frobenius on the stalk has a matrix, and
the local factor of that matrix is the basis-free local factor of the Frobenius endomorphism.

## Main definitions

* `Stacks.EtaleCohomology.lFunctionOfConstructibleFlat`: the L-function of a constructible flat
  `Λ`-module on the small étale site.

## Main results

* `Stacks.EtaleCohomology.finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf` and
  `Stacks.EtaleCohomology.projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf`: the
  stalks of a constructible flat sheaf at geometric points are finite projective.
* `Stacks.EtaleCohomology.charPowerSeries_frobeniusStalkEnd_eq_localFactor` and
  `Stacks.EtaleCohomology.coeff_lFunctionOfConstructibleFlat_eq`: the local factor of the
  L-function at a closed point is `det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄}) ⁻¹`, and the product of
  those factors computes the L-function coefficientwise.
* `Stacks.EtaleCohomology.lFunction_eq_lFunctionOfConstructibleFlat`: a family of Frobenius
  matrices whose local factors are those of the Frobenius action on the stalks of `ℱ` has the
  same Euler product, so the definition agrees with the matrix-fed one of
  `Stacks.EtaleCohomology.FrobeniusMatrices.lFunction`.
* `Stacks.EtaleCohomology.isUnit_lFunctionOfConstructibleFlat`: the L-function is a unit
  of `Λ⟦T⟧`.

## References

* [Stacks Project, Tag 03UV](https://stacks.math.columbia.edu/tag/03UV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w r

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (Λ : Type r) [CommRing Λ]
  [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)]
  [∀ (S T : B.Scheme) (g : T ⟶ S),
    ((smallEtaleBaseChange B g).sheafPushforwardContinuous (ModuleCat.{w} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V) (ModuleCat.{w} Λ)]
  (F : Sheaf (SmallEtale.topology B X.obj X.property) (ModuleCat.{w} Λ))

/-! ### The stalks of a constructible flat sheaf -/

omit [HasColimitsOfSize.{u, u} (ModuleCat.{w} Λ)] [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)] in
/-- A constructible flat sheaf is stratumwise locally constant with constant values that are finite
projective `Λ`-modules. -/
public theorem isStratifiedLocallyConstantWith_of_isConstructibleFlatModuleSheaf
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) :
    IsStratifiedLocallyConstantWith B X Λ
      (fun E => Module.Finite Λ E ∧ Module.Projective Λ E) F := by
  intro U
  obtain ⟨σ, hσ⟩ := hF U
  refine ⟨σ, fun i V => ?_⟩
  obtain ⟨I, W, g, hcov, hloc⟩ := hσ i V
  refine ⟨I, W, g, hcov, fun j => ?_⟩
  obtain ⟨E, hfin, hproj, he⟩ := hloc j
  exact ⟨E, ⟨hfin, hproj⟩, he⟩

omit [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)] in
/-- **The stalks of a constructible flat sheaf are finite projective**: the stalk at a geometric
point is a finite projective `Λ`-module. -/
public theorem finite_and_projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) (s : GeometricPoint X.obj) :
    Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj F) ∧
      Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F) :=
  stalk_prop_of_isStratifiedLocallyConstantWith B X Λ _
    (fun e ⟨_, _⟩ =>
      ⟨Module.Finite.equiv e.toLinearEquiv, Module.Projective.of_equiv e.toLinearEquiv⟩)
    (fun _ _ => ⟨inferInstance, inferInstance⟩)
    F (isStratifiedLocallyConstantWith_of_isConstructibleFlatModuleSheaf B X Λ F hF) s

omit [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)] in
/-- The stalk of a constructible flat sheaf at a geometric point is a finite `Λ`-module. -/
public theorem finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) (s : GeometricPoint X.obj) :
    Module.Finite Λ ((etaleModuleStalkFunctor B X Λ s).obj F) :=
  (finite_and_projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF s).1

omit [HasLimitsOfSize.{u, u} (ModuleCat.{w} Λ)] in
/-- The stalk of a constructible flat sheaf at a geometric point is a projective `Λ`-module. -/
public theorem projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf
    (hF : IsConstructibleFlatModuleSheaf B X Λ F) (s : GeometricPoint X.obj) :
    Module.Projective Λ ((etaleModuleStalkFunctor B X Λ s).obj F) :=
  (finite_and_projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF s).2

/-! ### The L-function -/

variable [IsLocalRing Λ] {k : Type u} [Field k] [Finite k] (f : X.obj ⟶ Spec (.of k))
  [LocallyOfFiniteType f] (hF : IsConstructibleFlatModuleSheaf B X Λ F)

/-- The family of Frobenius matrices of a constructible flat sheaf: the rank and the matrix at a
closed point are those of the geometric Frobenius on the stalk, which is finite projective. -/
public def frobeniusMatricesOfConstructibleFlat : FrobeniusMatrices f Λ :=
  frobeniusMatricesOfSheaf B X Λ F f
    (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)
    (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)

/-- **The L-function of a constructible flat `Λ`-module over a local coefficient ring.** It is
the Euler product over the closed points of `X` of the inverse local factors
`det(1 - π_x^* T ^ (deg x) |_{ℱ_x̄}) ⁻¹` of the geometric Frobenius acting on the stalks of `ℱ`,
computed from the matrices of the Frobenius in bases of the (free) stalks. The L-function of
Tag 03UV for an arbitrary coefficient ring, not necessarily local, is
`Stacks.EtaleCohomology.constructibleFlatLFunction`, which agrees with this one when `Λ` is local
(`Stacks.EtaleCohomology.constructibleFlatLFunction_eq_lFunctionOfConstructibleFlat`). -/
@[sga "4½ Rapport 1.6" "L-function of a sheaf"]
public def lFunctionOfConstructibleFlat [QuasiCompact f] : PowerSeries Λ :=
  (frobeniusMatricesOfConstructibleFlat B X Λ F f hF).lFunction

/-- The local factor of the L-function at a closed point is the inverse of the basis-free local
factor `det(1 - π_x^* T ^ (deg x))` of the geometric Frobenius on the stalk there. -/
public theorem charPowerSeries_frobeniusStalkEnd_eq_localFactor (x : closedPoints X.obj) :
    (frobeniusMatricesOfConstructibleFlat B X Λ F f hF).localFactor x =
      PowerSeries.invOfUnit
        (charPowerSeries (frobeniusStalkEnd B X Λ F f x) (residueDegree f x.1)) 1 := by
  have h := charPowerSeries_frobeniusStalkEnd B X Λ F f
    (finite_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF)
    (projective_etaleModuleStalk_of_isConstructibleFlatModuleSheaf B X Λ F hF) x
    (residueDegree f x.1)
  rw [FrobeniusMatrices.localFactor, localEulerFactor]
  exact congrArg (fun p => PowerSeries.invOfUnit p 1) h.symm

/-- **The defining product converges.** The coefficient of `T ^ j` of `L(X, ℱ)` is the
coefficient of `T ^ j` of the product of the local factors `det(1 - π_x^* T ^ (deg x)) ⁻¹` over
any finite set of closed points containing those of degree at most `j`. -/
public theorem coeff_lFunctionOfConstructibleFlat_eq [QuasiCompact f] {j : ℕ}
    {t : Finset (closedPoints X.obj)}
    (ht : (frobeniusMatricesOfConstructibleFlat B X Λ F f hF).eulerSystem.support j ⊆ t) :
    PowerSeries.coeff j (lFunctionOfConstructibleFlat B X Λ F f hF) =
      PowerSeries.coeff j (∏ x ∈ t, PowerSeries.invOfUnit
        (charPowerSeries (frobeniusStalkEnd B X Λ F f x) (residueDegree f x.1)) 1) :=
  ((frobeniusMatricesOfConstructibleFlat B X Λ F f hF).coeff_lFunction_eq ht).trans
    (congrArg _ (Finset.prod_congr rfl fun x _ =>
      charPowerSeries_frobeniusStalkEnd_eq_localFactor B X Λ F f hF x))

/-- **The L-function of a constructible flat sheaf is the matrix-fed Euler product.** Any family
of Frobenius matrices whose local factors at the closed points are the local factors of the
geometric Frobenius on the stalks of `ℱ` has the L-function of `ℱ` as its Euler product. -/
public theorem lFunction_eq_lFunctionOfConstructibleFlat [QuasiCompact f]
    (D : FrobeniusMatrices f Λ)
    (hD : ∀ x : closedPoints X.obj, localCharSeries (D.matrix x) (residueDegree f x.1) =
      charPowerSeries (frobeniusStalkEnd B X Λ F f x) (residueDegree f x.1)) :
    D.lFunction = lFunctionOfConstructibleFlat B X Λ F f hF :=
  D.lFunction_congr fun x => by
    rw [charPowerSeries_frobeniusStalkEnd_eq_localFactor B X Λ F f hF x,
      FrobeniusMatrices.localFactor, localEulerFactor, hD x]

/-- The L-function of a constructible flat sheaf is a unit of `Λ⟦T⟧`. -/
public theorem isUnit_lFunctionOfConstructibleFlat [QuasiCompact f] :
    IsUnit (lFunctionOfConstructibleFlat B X Λ F f hF) :=
  FrobeniusMatrices.isUnit_lFunction _

end Stacks.EtaleCohomology

end
