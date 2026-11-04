module

public import StacksFrontier.AlgebraicGeometry.Curves.FittingIdealJacobianMinors
public import StacksFrontier.RingTheory.CompleteLocalRing.QuotientNodal.NodalQuadraticRelationTransport

/-!
# The nodal quadratic relation of a local ring is read off its power-series model

Let `A` be an `R`-algebra presented by `n` generators lying in a maximal ideal `p` and `m`
relations, let `e : R ≃+* K` with `K` a field, and let `A_p` be the localization of `A` at `p`.
The power-series model of the presentation is `T = K[[x_1, …, x_n]] / (f)`, for the relations
transported along `e`. Then `A_p` carries a nodal quadratic relation exactly when `T` does.

Both `A_p` and `T` are quotients of `K[x_1, …, x_n]` modulo the cube of the maximal ideal, by one
and the same ideal `(f) + (x_1, …, x_n) ^ 3`: localizing at `p` does not change the quotient by
`p ^ 3`, and completing does not change the quotient by `𝔪 ^ 3`. Since the nodal quadratic
relation is a condition modulo the cube of the maximal ideal, it transfers.

## Main results

* `Stacks.Curves.presentationHom` — the structure map of a presentation read over `K`, with its
  kernel, its image of the maximal ideal, and the resulting bound on the relations.
* `Stacks.Curves.hasNodalQuadraticRelation_iff_of_ker_eq` — two local rings whose quotients by
  the cubes of their maximal ideals are presented by one ring with the same kernel carry the same
  nodal quadratic relation.
* `Stacks.Curves.hasNodalQuadraticRelation_atPrime_iff_powerSeriesModel` — the localization at
  `p` and the power-series model of the presentation carry the same nodal quadratic relation.

## Implementation notes

A presentation whose generators lie in `p` forces the residue field at `p` to be `K`: the
preimage of `p` in the polynomial ring is the ideal of variables
(`Stacks.Curves.comap_presentationHom`), so `A / p ≅ K`. This is the same restriction under which
`Stacks.Curves.sup_sq_eq_iff_jacobianMinorIdealModulo_of_ringEquiv` states the Jacobian condition.

The two computations of the kernel are
`IsLocalRing.ker_quotient_pow_comp_algebraMap` on the localization side and
`Stacks.MvPowerSeries.ker_mk_pow_comp_coe` on the power-series side; the transfer of the relation
itself is `Stacks.Curves.hasNodalQuadraticRelation_iff_of_ker_le_cube`.

## References

* [Stacks Project, Tag 0C4C](https://stacks.math.columbia.edu/tag/0C4C)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
-/

@[expose] public section

open Algebra MvPolynomial IsLocalRing

namespace Stacks.Curves

universe u

variable {R : Type u} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  (K : Type u) [Field K] (e : R ≃+* K) {n m : ℕ}
  (P : Algebra.Presentation R A (Fin n) (Fin m)) {p : Ideal A} [p.IsMaximal]

/-! ### The structure map of a presentation, read over a field -/

/-- The structure map of a presentation read over `K`: it is the structure map of the
presentation precomposed with the isomorphism of polynomial rings induced by `e⁻¹`. -/
noncomputable def presentationHom : MvPolynomial (Fin n) K →+* A :=
  (aeval (R := R) P.val).toRingHom.comp (MvPolynomial.mapEquiv (Fin n) e).symm.toRingHom

/-- The structure map of a presentation read over `K` is surjective. -/
theorem surjective_presentationHom : Function.Surjective (presentationHom K e P) :=
  P.aeval_val_surjective.comp (MvPolynomial.mapEquiv (Fin n) e).symm.surjective

/-- The kernel of the structure map read over `K` is spanned by the transported relations. -/
theorem ker_presentationHom :
    RingHom.ker (presentationHom K e P) =
      Ideal.span (Set.range fun j => MvPolynomial.map (e : R →+* K) (P.relation j)) := by
  have hker : RingHom.ker (aeval (R := R) P.val).toRingHom =
      Ideal.span (Set.range P.relation) := by
    rw [P.span_range_relation_eq_ker, Algebra.Generators.ker_eq_ker_aeval_val]
    rfl
  rw [presentationHom, ← RingHom.comap_ker, RingEquiv.toRingHom_eq_coe, Ideal.comap_coe,
    Ideal.comap_symm, hker, Ideal.map_span, ← Set.range_comp]
  rfl

/-- The isomorphism of polynomial rings induced by `e` carries the ideal of variables to the
ideal of variables. -/
theorem map_mapEquiv_idealOfVars :
    Ideal.map (MvPolynomial.mapEquiv (Fin n) e) (MvPolynomial.idealOfVars (Fin n) R) =
      MvPolynomial.idealOfVars (Fin n) K := by
  rw [← Ideal.map_coe, ← RingEquiv.toRingHom_eq_coe]
  exact map_idealOfVars_mapEquiv e n

/-- For a presentation whose generators lie in a maximal ideal `p`, the preimage of `p` under the
structure map read over `K` is the ideal of variables: the presentation is centred at `p`. -/
theorem comap_presentationHom (hv : ∀ i, P.val i ∈ p) :
    p.comap (presentationHom K e P) = MvPolynomial.idealOfVars (Fin n) K := by
  have hsurj : Function.Surjective (aeval (R := R) P.val) := P.aeval_val_surjective
  have hqmax : (p.comap (aeval (R := R) P.val).toRingHom).IsMaximal :=
    Ideal.comap_isMaximal_of_surjective _ hsurj
  have hvars : MvPolynomial.idealOfVars (Fin n) R ≤ p.comap (aeval (R := R) P.val).toRingHom := by
    rw [MvPolynomial.idealOfVars, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simpa [Ideal.mem_comap] using hv i
  have hstep : p.comap (presentationHom K e P) =
      Ideal.map (MvPolynomial.mapEquiv (Fin n) e)
        (p.comap (aeval (R := R) P.val).toRingHom) := by
    rw [presentationHom, ← Ideal.comap_comap, RingEquiv.toRingHom_eq_coe, Ideal.comap_coe,
      Ideal.comap_symm]
  rw [hstep]
  refine ((isMaximal_idealOfVars_fin (k := K) n).eq_of_le ?_ ?_).symm
  · intro htop
    refine hqmax.ne_top ?_
    have hc := congrArg (Ideal.comap (MvPolynomial.mapEquiv (Fin n) e)) htop
    rwa [Ideal.comap_map_of_bijective (MvPolynomial.mapEquiv (Fin n) e)
      (MvPolynomial.mapEquiv (Fin n) e).bijective, Ideal.comap_top] at hc
  · rw [← map_mapEquiv_idealOfVars K e]
    exact Ideal.map_mono hvars

/-- For a presentation whose generators lie in a maximal ideal, the transported relations lie in
the ideal of variables. -/
theorem span_range_map_relation_le_idealOfVars (hv : ∀ i, P.val i ∈ p) :
    Ideal.span (Set.range fun j => MvPolynomial.map (e : R →+* K) (P.relation j)) ≤
      MvPolynomial.idealOfVars (Fin n) K := by
  rw [← ker_presentationHom K e P, ← comap_presentationHom K e P (p := p) hv]
  intro z hz
  rw [RingHom.mem_ker] at hz
  rw [Ideal.mem_comap, hz]
  exact p.zero_mem

/-! ### Transferring the nodal quadratic relation -/

/-- Quotienting a local ring by an ideal inside the cube of its maximal ideal preserves the
nodal quadratic relation. -/
private theorem hasNodalQuadraticRelation_quotient_iff {B : Type u} [CommRing B] [IsLocalRing B]
    {I : Ideal B} [IsLocalRing (B ⧸ I)] (hI : I ≤ maximalIdeal B ^ 3) :
    HasNodalQuadraticRelation B ↔ HasNodalQuadraticRelation (B ⧸ I) :=
  hasNodalQuadraticRelation_iff_of_surjective_of_ker_le_cube (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])

/-- **A nodal quadratic relation is determined by a presentation of the quotient by the cube of
the maximal ideal.** If one ring surjects onto `B ⧸ I_B` and onto `C ⧸ I_C`, with `I_B` and `I_C`
inside the cubes of the maximal ideals and with equal kernels, then `B` carries a nodal quadratic
relation exactly when `C` does. -/
theorem hasNodalQuadraticRelation_iff_of_ker_eq
    {Q B C : Type u} [CommRing Q] [CommRing B] [CommRing C] [IsLocalRing B] [IsLocalRing C]
    {IB : Ideal B} {IC : Ideal C} (hIB : IB ≤ maximalIdeal B ^ 3)
    (hIC : IC ≤ maximalIdeal C ^ 3) {f : Q →+* B ⧸ IB} {g : Q →+* C ⧸ IC}
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : RingHom.ker f = RingHom.ker g) :
    HasNodalQuadraticRelation B ↔ HasNodalQuadraticRelation C := by
  have : IsLocalRing (B ⧸ IB) := isLocalRing_quotient_of_le_maximalIdeal IB
    (hIB.trans (Ideal.pow_le_self (by norm_num)))
  have : IsLocalRing (C ⧸ IC) := isLocalRing_quotient_of_le_maximalIdeal IC
    (hIC.trans (Ideal.pow_le_self (by norm_num)))
  exact (hasNodalQuadraticRelation_quotient_iff hIB).trans
    ((hasNodalQuadraticRelation_congr
      ((RingHom.quotientKerEquivOfSurjective hf).symm.trans
        ((Ideal.quotEquivOfEq h).trans (RingHom.quotientKerEquivOfSurjective hg)))).trans
      (hasNodalQuadraticRelation_quotient_iff hIC).symm)

/-- **The local ring at a rational point and its power-series model carry the same nodal
quadratic relation.** Let `A` be an `R`-algebra presented by `n` generators lying in a maximal
ideal `p` and `m` relations, let `e : R ≃+* K` with `K` a field, and let `A_p` be the
localization of `A` at `p`. Then `A_p` carries a nodal quadratic relation exactly when
`K[[x_1, …, x_n]] / (f)` does, for the relations `f` transported along `e`. -/
theorem hasNodalQuadraticRelation_atPrime_iff_powerSeriesModel (hv : ∀ i, P.val i ∈ p)
    (Ap : Type u) [CommRing Ap] [Algebra A Ap] [IsLocalization.AtPrime Ap p] [IsLocalRing Ap]
    [IsLocalRing (MvPowerSeries (Fin n) K ⧸
      (Ideal.span (Set.range fun j => MvPolynomial.map (e : R →+* K) (P.relation j))).map
        (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := K)))] :
    HasNodalQuadraticRelation Ap ↔
      HasNodalQuadraticRelation (MvPowerSeries (Fin n) K ⧸
        (Ideal.span (Set.range fun j => MvPolynomial.map (e : R →+* K) (P.relation j))).map
          (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := K))) := by
  have hJle : Ideal.span (Set.range fun j => MvPolynomial.map (e : R →+* K) (P.relation j)) ≤
      MvPolynomial.idealOfVars (Fin n) K :=
    span_range_map_relation_le_idealOfVars K e P (p := p) hv
  refine hasNodalQuadraticRelation_iff_of_ker_eq
    (le_of_eq (maximalIdeal_pow_eq_map_pow p Ap 3).symm) le_rfl
    (f := ((Ideal.Quotient.mk ((p ^ 3).map (algebraMap A Ap))).comp (algebraMap A Ap)).comp
      (presentationHom K e P))
    (g := ((Ideal.Quotient.mk (maximalIdeal (MvPowerSeries (Fin n) K ⧸
          (Ideal.span (Set.range fun j =>
            MvPolynomial.map (e : R →+* K) (P.relation j))).map
            (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := K))) ^ 3)).comp
        (Ideal.Quotient.mk _)).comp
      (MvPolynomial.coeToMvPowerSeries.ringHom (σ := Fin n) (R := K)))
    ((surjective_quotient_pow_comp_algebraMap p Ap 3).comp (surjective_presentationHom K e P))
    (Stacks.MvPowerSeries.surjective_mk_pow_comp_coe _ Ideal.Quotient.mk_surjective 3) ?_
  rw [Stacks.MvPowerSeries.ker_mk_pow_comp_coe hJle _ Ideal.Quotient.mk_surjective Ideal.mk_ker
      (by norm_num : 1 ≤ 3),
    ← RingHom.comap_ker, ker_quotient_pow_comp_algebraMap p Ap 3]
  have hp : p = Ideal.map (presentationHom K e P) (MvPolynomial.idealOfVars (Fin n) K) := by
    rw [← comap_presentationHom K e P (p := p) hv]
    exact (Ideal.map_comap_of_surjective (presentationHom K e P)
      (surjective_presentationHom K e P) p).symm
  rw [hp, ← Ideal.map_pow,
    Ideal.comap_map_of_surjective _ (surjective_presentationHom K e P),
    ← RingHom.ker_eq_comap_bot, ker_presentationHom K e P, sup_comm]

end Stacks.Curves

end
