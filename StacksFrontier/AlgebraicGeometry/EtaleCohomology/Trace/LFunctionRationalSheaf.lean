module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.FrobeniusStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.StalkFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.SheafFrobeniusMatrices
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The L-function of a `ℚ_ℓ`-sheaf

Let `X` be a scheme of finite type over a finite field `k` and let `F` be a `ℚ_ℓ`-sheaf on `X`,
that is (Tag 03UR) a `ℤ_ℓ`-sheaf read in the quotient of the category of `ℤ_ℓ`-sheaves by the
torsion ones, whose stalk at a geometric point `x̄` is `F_x̄ = ℚ_ℓ ⊗_{ℤ_ℓ} F'_x̄`. Its L-function
is

`L(X, F) = ∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) | F_x̄) ⁻¹ ∈ ℚ_ℓ⟦T⟧`,

the product running over the closed points `|X|` of `X`, with `deg x = [κ(x) : k]` and `π_x^*` the
geometric Frobenius at `x` acting on the stalk at a geometric point over `x`.

The geometric point at a closed point `x` and the geometric Frobenius `π_x^*` as an endomorphism of
it are `Stacks.Frobenius.geometricPointAt` and `Stacks.Frobenius.frobeniusPointHom`; the action of
such an endomorphism on the rational stalk is `LAdicSheaf.rationalStalkEnd`. The stalk is a
finite-dimensional `ℚ_ℓ`-vector space, because the `ℓ`-adic stalk is a finite `ℤ_ℓ`-module, so the
Frobenius has a matrix there and the local factor is its characteristic series; the local factor
does not depend on the basis chosen, by `charPowerSeries_eq_localCharSeries_matrixOf`.

The infinite product is not a limit in `ℚ_ℓ⟦T⟧`, which has none. The local factor at a point of
degree `d` is congruent to `1` modulo `T ^ d` and there are only finitely many closed points of
degree at most `n` for each `n` — the two hypotheses of `EulerSystem` — so the coefficient of
`T ^ n` of the product is computed by the finite subproduct over the points of degree at most `n`,
and by `EulerSystem.coeff_eulerProduct_eq` by any finite subproduct containing those. That is the
precise form of the convergence asserted by Tag 03UX, and it is `coeff_rationalLFunction_eq`
below. Both finiteness hypotheses are theorems here, not assumptions: the degrees are positive by
`residueDegree_pos` and the points of bounded degree are finite in number by
`finite_setOf_closedPoints_residueDegree_le`.

## Main definitions

* `Stacks.EtaleCohomology.LAdicSheaf.rationalStalkFrobenius`: the geometric Frobenius `π_x^*` at a
  closed point `x`, acting on the rational stalk at the geometric point there.
* `Stacks.EtaleCohomology.LAdicSheaf.frobeniusMatrices`: its matrices at all the closed points.
* `Stacks.EtaleCohomology.LAdicSheaf.rationalLFunction`: the L-function `L(X, F)` in `ℚ_ℓ⟦T⟧`.

## Main results

* `Stacks.EtaleCohomology.LAdicSheaf.localCharSeries_frobeniusMatrices` and
  `Stacks.EtaleCohomology.LAdicSheaf.localFactor_frobeniusMatrices`: the factor of the product at
  `x` is `det(1 - π_x^* T ^ (deg x) | F_x̄) ⁻¹`, written basis-free.
* `Stacks.EtaleCohomology.LAdicSheaf.coeff_rationalLFunction_eq`: the product converges, in the
  sense that each coefficient is computed by any large enough finite subproduct.
* `Stacks.EtaleCohomology.LAdicSheaf.isUnit_rationalLFunction`: the L-function is a unit of
  `ℚ_ℓ⟦T⟧`.

## References

* [Stacks Project, Tag 03UX](https://stacks.math.columbia.edu/tag/03UX)
* [Stacks Project, Tag 03UR](https://stacks.math.columbia.edu/tag/03UR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry AlgebraicGeometry.SmallEtale CategoryTheory CategoryTheory.Limits
  Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

variable (B : BigEtaleSite.{u}) (X : B.Scheme) (ℓ : ℕ)

variable [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
  ((smallEtaleBaseChange B f).sheafPushforwardContinuous
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
    (SmallEtale.topology B S.1 S.property)
    (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
variable [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
  HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [∀ n : ℕ, HasWeakSheafify
  (SmallEtale.topology B X.1 X.property)
  (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
variable [IsNoetherian X.1] [Fact ℓ.Prime]

/-! ### The geometric Frobenius on the rational stalk -/

/-- The geometric Frobenius `π_x^*` at a point `x` with finite residue field, acting on the
rational stalk `ℚ_ℓ ⊗_{ℤ_ℓ} F_x̄` of a `ℚ_ℓ`-sheaf at the geometric point at `x`: the action on
the rational stalk of the geometric Frobenius of `κ(x)`, read as an endomorphism of that geometric
point. -/
public def LAdicSheaf.rationalStalkFrobenius (F : LAdicSheaf B X ℓ) (x : X.1)
    (hx : Finite (X.1.residueField x)) :
    LAdicSheaf.rationalStalkLeft B X ℓ F (geometricPointAt X.1 x) →ₗ[Padic ℓ]
      LAdicSheaf.rationalStalkLeft B X ℓ F (geometricPointAt X.1 x) :=
  haveI := hx
  LAdicSheaf.rationalStalkEnd B X ℓ F (frobeniusPointHom X.1 x)

/-! ### The L-function -/

variable {k : Type u} [Field k] [Finite k]

/-- The matrices of the geometric Frobenius actions on the rational stalks of a `ℚ_ℓ`-sheaf at the
closed points of `X`.  The rank at `x` is the dimension over `ℚ_ℓ` of the rational stalk there,
which is finite because the `ℓ`-adic stalk is a finite `ℤ_ℓ`-module. -/
public def LAdicSheaf.frobeniusMatrices (F : LAdicSheaf B X ℓ) (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] : FrobeniusMatrices f (Padic ℓ) where
  rank x := rankOf (Padic ℓ) (LAdicSheaf.rationalStalkLeft B X ℓ F (geometricPointAt X.1 x.1))
  matrix x := matrixOf (Padic ℓ)
    (LAdicSheaf.rationalStalkLeft B X ℓ F (geometricPointAt X.1 x.1))
    (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2))

/-- The local factor of the matrix at `x` is the basis-free local factor
`det(1 - π_x^* T ^ d | F_x̄)` of the geometric Frobenius on the rational stalk, so the choice of a
basis in which to write `π_x^*` is immaterial. -/
public theorem LAdicSheaf.localCharSeries_frobeniusMatrices (F : LAdicSheaf B X ℓ)
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : closedPoints X.1) (d : ℕ) :
    localCharSeries ((LAdicSheaf.frobeniusMatrices B X ℓ F f).matrix x) d =
      charPowerSeries
        (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2)) d :=
  (charPowerSeries_eq_localCharSeries_matrixOf (Padic ℓ) _ _ d).symm

/-- The factor of the Euler product at a closed point `x` is
`det(1 - π_x^* T ^ (deg x) | F_x̄) ⁻¹`. -/
@[sga "4½ Rapport 1.6" "special case"]
public theorem LAdicSheaf.localFactor_frobeniusMatrices (F : LAdicSheaf B X ℓ)
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : closedPoints X.1) :
    (LAdicSheaf.frobeniusMatrices B X ℓ F f).localFactor x =
      PowerSeries.invOfUnit
        (charPowerSeries
          (LAdicSheaf.rationalStalkFrobenius B X ℓ F x.1 (finite_residueField f x.1 x.2))
          (residueDegree f x.1)) 1 := by
  rw [FrobeniusMatrices.localFactor, localEulerFactor,
    LAdicSheaf.localCharSeries_frobeniusMatrices]

/-- The L-function of a `ℚ_ℓ`-sheaf `F` on a scheme `X` of finite type over a finite field `k`:

`L(X, F) = ∏_{x ∈ |X|} det(1 - π_x^* T ^ (deg x) | F_x̄) ⁻¹ ∈ ℚ_ℓ⟦T⟧`,

the product over the closed points `|X|` of `X` of the inverse characteristic series of the
geometric Frobenius `π_x^*` acting on the rational stalk `F_x̄` at a geometric point over `x`,
where `deg x = [κ(x) : k]`.  The factor at `x` is identified with
`det(1 - π_x^* T ^ (deg x) | F_x̄) ⁻¹` by `localFactor_frobeniusMatrices`, and the product
converges in the sense of `coeff_rationalLFunction_eq`: there are finitely many closed points of
any given degree, so each coefficient is already computed by a finite subproduct. -/
@[stacks 03UX "the definition of L(X, F) for a Q_ell-sheaf F, as the Euler product over the \
closed points of the inverse characteristic series of the geometric Frobenius on the rational \
stalks",
  sga "4½ Rapport 1.6" "adic coefficients"]
public def LAdicSheaf.rationalLFunction (F : LAdicSheaf B X ℓ) (f : X.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] : PowerSeries (Padic ℓ) :=
  (LAdicSheaf.frobeniusMatrices B X ℓ F f).lFunction

/-- The convergence of the defining product: the coefficient of `T ^ j` of `L(X, F)` is computed
by the product of the local factors over any finite set of closed points containing all those of
degree at most `j`. -/
@[stacks 03UX "the product converges since there are finitely many points of a given degree"]
public theorem LAdicSheaf.coeff_rationalLFunction_eq (F : LAdicSheaf B X ℓ)
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f]
    {j : ℕ} {t : Finset (closedPoints X.1)}
    (ht : (LAdicSheaf.frobeniusMatrices B X ℓ F f).eulerSystem.support j ⊆ t) :
    PowerSeries.coeff j (LAdicSheaf.rationalLFunction B X ℓ F f) =
      PowerSeries.coeff j
        (∏ x ∈ t, (LAdicSheaf.frobeniusMatrices B X ℓ F f).localFactor x) :=
  FrobeniusMatrices.coeff_lFunction_eq _ ht

/-- The L-function of a `ℚ_ℓ`-sheaf has constant coefficient `1`. -/
public theorem LAdicSheaf.constantCoeff_rationalLFunction (F : LAdicSheaf B X ℓ)
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    PowerSeries.constantCoeff (LAdicSheaf.rationalLFunction B X ℓ F f) = 1 :=
  FrobeniusMatrices.constantCoeff_lFunction _

/-- The L-function of a `ℚ_ℓ`-sheaf is a unit of `ℚ_ℓ⟦T⟧`. -/
public theorem LAdicSheaf.isUnit_rationalLFunction (F : LAdicSheaf B X ℓ)
    (f : X.1 ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] :
    IsUnit (LAdicSheaf.rationalLFunction B X ℓ F f) :=
  FrobeniusMatrices.isUnit_lFunction _

end Stacks.EtaleCohomology

end
