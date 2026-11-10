module

public import StacksFrontier.AlgebraicGeometry.Curves.JacobianCriterionReduction
public import StacksFrontier.AlgebraicGeometry.Curves.NodalRelationPowerSeriesModel
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.DifferentialsJacobian

/-!
# The first Fitting ideal of the differentials and the nodal quadratic relation

Let `f : X ⟶ S` be locally of finite type, let `x` be a closed point of `X` lying in an affine
open `Spec A = U` over an affine open `Spec R = V` with `R` Noetherian and isomorphic to a field
`K`, and let `A` be presented over `R` by `n` generators lying in the prime of `x` and `m`
relations. Then the stalk at `x` of the first Fitting ideal sheaf of `Ω_{X/S}` is the maximal
ideal of `𝒪_{X,x}` exactly when `𝒪_{X,x}` carries a nodal quadratic relation on its cotangent
space.

Since `Stacks.Curves.IsNodalAlgebra` is separability of the residue field together with
reducedness and the nodal quadratic relation, this is the equivalence of conditions (2) and (4)
of Tag 0C4D: the two conditions share their separability and reducedness clauses, and differ
only in the nodal relation against the Fitting-ideal condition.

## Main results

* `Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation` — the
  Fitting-ideal condition at `x` is the nodal quadratic relation on `𝒪_{X,x}`.
* `Stacks.Curves.isNodalAlgebra_stalk_iff_isReduced_and_stalk_fittingIdeal_eq_maximalIdeal` —
  hence conditions (2) and (4) of Tag 0C4D are equivalent.

## Implementation notes

The three links of the chain are
`AlgebraicGeometry.stalk_fittingIdeal_eq_maximalIdeal_iff_jacobianMinorIdealModulo`, which turns
the Fitting-ideal condition into the Jacobian condition of Tag 0C4C for the power-series model
of the presentation; the Jacobian-versus-relation equivalence
`jacobianMinorIdealModulo_eq_maximalIdeal_iff_hasNodalQuadraticRelation_of_le_maximalIdeal`
of this namespace, which is Tag 0C4C itself; and
`Stacks.Curves.hasNodalQuadraticRelation_atPrime_iff_powerSeriesModel`, which carries the nodal
relation between the power-series model and the local ring at `x`.

A presentation of the chart whose generators lie in the prime of `x` forces the residue field at
`x` to be `K`: this is the rational-point case of the tag, and is the case in which the Jacobian
condition of Tag 0C4C may be read in the power-series model. It is the only hypothesis on the
presentation: nothing is assumed about where the Jacobian minors lie, neither that the
`(n - 1)`-minors lie
in the ideal of variables upstairs nor that they lie in the prime of the point downstairs. Such
assumptions would be no restriction, because a minor
outside the prime is a unit in `𝒪_{X,x}` and makes the Fitting-ideal condition fail on both
sides of every equivalence in the chain; the two statements of
`StacksFrontier.RingTheory.CompleteLocalRing.IdealsUnderCompletion` and
`StacksFrontier.RingTheory.MvPowerSeries.PolynomialCotangent` dispose of that case themselves.

## References

* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
* [Stacks Project, Tag 0C4C](https://stacks.math.columbia.edu/tag/0C4C)
* [Stacks Project, Tag 0C49](https://stacks.math.columbia.edu/tag/0C49)
-/

@[expose] public section

open CategoryTheory Algebra MvPolynomial IsLocalRing AlgebraicGeometry

namespace Stacks.Curves

universe u

/-- **The Fitting-ideal condition of Tag 0C4D is the nodal quadratic relation on the local
ring.** Let `f : X ⟶ S` be locally of finite type, `x` a closed point in an affine open
`Spec A = U` over an affine open `Spec R = V` with `R` Noetherian, and `e : R ≃+* K` an
isomorphism onto a field. For a presentation of `A` over `R` whose generators lie in the prime of
`x`, the stalk at `x` of the first Fitting ideal sheaf of `Ω_{X/S}` is the maximal ideal of
`𝒪_{X,x}` exactly when `𝒪_{X,x}` carries a nodal quadratic relation on its cotangent space. -/
theorem stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (U : X.affineOpens) (hxU : x ∈ U.1) (hx : IsClosed ({x} : Set X))
    {V : S.Opens} (hV : IsAffineOpen V) (hUV : (U : X.Opens) ≤ f ⁻¹ᵁ V)
    [IsNoetherianRing Γ(S, V)] (K : Type u) [Field K] (e : Γ(S, V) ≃+* K) :
    letI := Stacks.Smooth.algebraAppLE f hUV
    ∀ {n m : ℕ} (P : Algebra.Presentation Γ(S, V) Γ(X, U.1) (Fin n) (Fin m))
      (_hv : ∀ i, P.val i ∈ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal),
      (IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials f) (1 : ℤ)) x =
          maximalIdeal (X.presheaf.stalk x) ↔
        HasNodalQuadraticRelation (X.presheaf.stalk x)) := by
  let := Stacks.Smooth.algebraAppLE f hUV
  intro n m P hv
  have hmax : ((U.2.primeIdealOf ⟨x, hxU⟩).asIdeal).IsMaximal :=
    U.2.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hx
  have hJ : Ideal.span (Set.range fun j =>
        MvPolynomial.map (e : Γ(S, V) →+* K) (P.relation j)) ≤
      MvPolynomial.idealOfVars (Fin n) K :=
    span_range_map_relation_le_idealOfVars K e P (p := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) hv
  have : Nontrivial (MvPowerSeries (Fin n) K ⧸
      (Ideal.span (Set.range fun j =>
        MvPolynomial.map (e : Γ(S, V) →+* K) (P.relation j))).map
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := K))) :=
    Ideal.Quotient.nontrivial_iff.mpr (Stacks.MvPowerSeries.map_ne_top_of_le_idealOfVars hJ)
  have : IsLocalRing (MvPowerSeries (Fin n) K ⧸
      (Ideal.span (Set.range fun j =>
        MvPolynomial.map (e : Γ(S, V) →+* K) (P.relation j))).map
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := K))) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, hxU⟩ : U.1)
  have hloc : IsLocalization.AtPrime (X.presheaf.stalk x)
      (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal := U.2.isLocalization_stalk ⟨x, hxU⟩
  have hspan : Ideal.span (Set.range fun j =>
        ((MvPolynomial.map (e : Γ(S, V) →+* K) (P.relation j) : MvPowerSeries (Fin n) K))) =
      (Ideal.span (Set.range fun j =>
        MvPolynomial.map (e : Γ(S, V) →+* K) (P.relation j))).map
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := K)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  exact (stalk_fittingIdeal_eq_maximalIdeal_iff_jacobianMinorIdealModulo f 1 x U hxU hx
      hV hUV K e P hv hJ).trans
    ((jacobianMinorIdealModulo_eq_maximalIdeal_iff_hasNodalQuadraticRelation_of_le_maximalIdeal
        ((Ideal.span (Set.range fun j =>
          MvPolynomial.map (e : Γ(S, V) →+* K) (P.relation j))).map
          (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := K)))
        (Stacks.MvPowerSeries.map_le_maximalIdeal_of_le_idealOfVars hJ)
        (fun j => ((MvPolynomial.map (e : Γ(S, V) →+* K) (P.relation j) :
          MvPowerSeries (Fin n) K))) hspan).trans
      (hasNodalQuadraticRelation_atPrime_iff_powerSeriesModel K e P
        (p := (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal) hv (X.presheaf.stalk x)).symm)

/-- **Conditions (2) and (4) of Tag 0C4D are equivalent.** The local ring at a closed point `x`
is a nodal algebra over a base field `k` exactly when its residue field is separable over `k`, it
is reduced, and the stalk at `x` of the first Fitting ideal sheaf of `Ω_{X/S}` is its maximal
ideal.

The two conditions share their separability and reducedness clauses; what is proved here is that
the nodal quadratic relation on `𝒪_{X,x}` is the Fitting-ideal condition, which is
`Stacks.Curves.stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation`. The base field
`k` is not required to be the base of the morphism: no clause of either condition relates the two
beyond the `k`-algebra structure on `𝒪_{X,x}`, which is an argument. -/
@[stacks 0C4D "clauses (2) and (4), at a closed point of an affine chart admitting a \
presentation centred there"]
theorem isNodalAlgebra_stalk_iff_isReduced_and_stalk_fittingIdeal_eq_maximalIdeal
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (x : X)
    (U : X.affineOpens) (hxU : x ∈ U.1) (hx : IsClosed ({x} : Set X))
    {V : S.Opens} (hV : IsAffineOpen V) (hUV : (U : X.Opens) ≤ f ⁻¹ᵁ V)
    [IsNoetherianRing Γ(S, V)] (K : Type u) [Field K] (e : Γ(S, V) ≃+* K)
    (k : Type u) [Field k] [Algebra k (X.presheaf.stalk x)] :
    letI := Stacks.Smooth.algebraAppLE f hUV
    ∀ {n m : ℕ} (P : Algebra.Presentation Γ(S, V) Γ(X, U.1) (Fin n) (Fin m))
      (_hv : ∀ i, P.val i ∈ (U.2.primeIdealOf ⟨x, hxU⟩).asIdeal),
      (IsNodalAlgebra k (X.presheaf.stalk x) ↔
        Algebra.IsSeparableExtension k (ResidueField (X.presheaf.stalk x)) ∧
          IsReduced (X.presheaf.stalk x) ∧
            IdealSheafData.stalk (fittingIdeal (Scheme.Hom.relativeDifferentials f) (1 : ℤ)) x =
              maximalIdeal (X.presheaf.stalk x)) := by
  let := Stacks.Smooth.algebraAppLE f hUV
  intro n m P hv
  have key := stalk_fittingIdeal_eq_maximalIdeal_iff_hasNodalQuadraticRelation f x U hxU hx hV
    hUV K e P hv
  exact ⟨fun h => ⟨h.1, h.2.1, key.2 h.2.2⟩, fun h => ⟨h.1, h.2.1, key.1 h.2.2⟩⟩

end Stacks.Curves

end
