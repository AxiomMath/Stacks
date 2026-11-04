module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Etale.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.AdicCompletion.LocalRing
public import Mathlib.RingTheory.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximation
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.GRing.EssFiniteType
public import StacksFrontier.RingTheory.Nagata.PthRoot
public import StacksCore.Tactic.StacksAttribute

/-!
# Approximating a formal map by an actual map on an étale extension

Let `R` be a Noetherian ring, let `A` be a Noetherian `R`-algebra, let `B` be an `R`-algebra of
finite type, let `𝔭 ⊂ A` and
`𝔮 ⊂ B` be primes, and let `φ : B_𝔮 → (A_𝔭)^∧` be a local `R`-algebra map into the completion of
the local ring of `A` at `𝔭`. If `A_𝔭` is a G-ring then, for every `N ≥ 1`, `φ` is approximated
to order `N` by an *actual* `R`-algebra map `B → A'` into an étale extension of `A` at a prime
`𝔭'` over `𝔭` with the same residue field. This is the ring-theoretic content of the Artin
approximation theorem in the geometric form of Stacks 37.39.1 (Tag 0CAU): `Spec A' → Spec A` is
the elementary étale neighbourhood of the source, and `Spec A' → Spec B` the morphism to `Y`.

## Main definitions

* `StacksDraft.ArtinApproximation.Completion` is the completion of the local ring of a ring at a
  prime, and `StacksDraft.ArtinApproximation.completionComparison` the map between two such
  completions induced by a ring map carrying one prime into the other.
* `StacksDraft.ArtinApproximation.ArtinApproximationGRing` is the statement of Stacks 0CAR, the
  approximation property for G-rings, written out in full as a single `Prop`.
* `StacksDraft.ArtinApproximation.EtaleApproximation` is the data the main theorem produces.

## Main results

* `StacksDraft.ArtinApproximation.exists_etaleApproximation`: the affine case of Stacks 0CAU,
  conditional on `ArtinApproximationGRing`, and with no finiteness hypothesis on `A` beyond
  Noetherianness — which is what the first step of Stacks 0CAW needs.
* `StacksDraft.ArtinApproximation.exists_etaleApproximation_of_isGRing_base`: the same with the
  source's own hypothesis, that the local ring of the base at the image prime is a G-ring; the
  bridge is `StacksDraft.ArtinApproximation.isGRing_localization_atPrime`, i.e. Stacks 07PV.

## Implementation notes

*What is assumed and what is proved.* Stacks 0CAR is the only assumed input, and it is no longer
an assumption of the development: `StacksDraft.ArtinApproximation.artinApproximationGRing`
discharges `ArtinApproximationGRing` unconditionally, Theorem 16.13.2 (Tag 07QZ) being
`Stacks.Smoothing.exists_localEtaleSolution_of_isGRing` and Popescu's theorem (Tag 07GC) being
`Stacks.Smoothing.indSmooth_of_isRegularRingMap`. It is carried as a hypothesis here only to keep
this file independent of that development. Everything between 0CAR and the conclusion
is proved here: the finite presentation `B = R[x₁, …, x_n] / (F₁, …, F_m)` of `B` over the
Noetherian ring `R`, the base change of the system to `A`, the solution of the system in
`(A_𝔭)^∧` read off from `φ`, the construction of `B → A'` from the approximate solution, the
identification of the contraction of `𝔭'` as `𝔮`, and the agreement of the two maps out of `B_𝔮`.

*Where `N ≥ 1` is used.* Only to know that `𝔪_{𝔭'}^N` lies inside the maximal ideal, which is
what forces `B → A'` to carry `𝔭'` back to exactly `𝔮` — that is, what makes the constructed
morphism send the distinguished point to `y`. The approximation statement itself is uniform
in `N`.

*The comparison of completions.* The congruence is an identity in `(A'_{𝔭'})^∧`, so the given
element of `(A_𝔭)^∧` has to be pushed forward along `A_𝔭 → A'_{𝔭'}`. Mathlib's `AdicCompletion`
API has no functoriality for a map of rings along a map of ideals; the required map is
`Stacks.Nagata.PthRootDescent.mapAdicCompletion`, which already exists in this development, and
`completionComparison` is its specialisation to local rings at primes.

## References

* [Stacks Project, Tag 0CAU](https://stacks.math.columbia.edu/tag/0CAU)
* [Stacks Project, Tag 0CAR](https://stacks.math.columbia.edu/tag/0CAR)
* [Stacks Project, Tag 07PV](https://stacks.math.columbia.edu/tag/07PV)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-! ### Completions of local rings at primes, and the maps between them -/

/-- The completion of the local ring of `A` at a prime `p`. -/
abbrev Completion {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] : Type u :=
  AdicCompletion (maximalIdeal (Localization.AtPrime p)) (Localization.AtPrime p)

/-- The canonical map from the local ring at `p` to its completion. -/
noncomputable abbrev ofLocalization {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] :
    Localization.AtPrime p →+* Completion p :=
  algebraMap (Localization.AtPrime p) (Completion p)

/-- The canonical map from `A` to the completion of its local ring at `p`. -/
noncomputable abbrev toCompletion {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime] :
    A →+* Completion p :=
  (ofLocalization p).comp (algebraMap A (Localization.AtPrime p))

/-- The `N`-th power of the maximal ideal of `Completion p`, written as the extension of the
`N`-th power of the maximal ideal of the local ring at `p`. -/
noncomputable abbrev completionIdeal {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    (N : ℕ) : Ideal (Completion p) :=
  Ideal.map (ofLocalization p) (maximalIdeal (Localization.AtPrime p) ^ N)

/-- The map of completed local rings induced by a ring map `g : A →+* B` at a prime `q` of `B`
whose contraction to `A` is `p`. -/
noncomputable def completionComparison {A B : Type u} [CommRing A] [CommRing B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (g : A →+* B) (hpq : p = q.comap g) :
    Completion p →+* Completion q :=
  letI : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q g hpq).toAlgebra
  Stacks.Nagata.PthRootDescent.mapAdicCompletion (maximalIdeal (Localization.AtPrime p))
    (maximalIdeal (Localization.AtPrime q))
    (by
      let := Localization.isLocalHom_localRingHom p q g hpq
      exact IsLocalRing.map_maximalIdeal_le (Localization.localRingHom p q g hpq))

/-- On the image of the local ring at `p`, `completionComparison` agrees with the induced map
`Localization.localRingHom` of local rings followed by `ofLocalization q`. -/
theorem completionComparison_ofLocalization {A B : Type u} [CommRing A] [CommRing B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (g : A →+* B) (hpq : p = q.comap g)
    (x : Localization.AtPrime p) :
    completionComparison p q g hpq (ofLocalization p x) =
      ofLocalization q (Localization.localRingHom p q g hpq x) := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q g hpq).toAlgebra
  exact Stacks.Nagata.PthRootDescent.mapAdicCompletion_of _ x

/-- On `A`, `completionComparison` sends `toCompletion p x` to `toCompletion q (g x)`. -/
theorem completionComparison_toCompletion {A B : Type u} [CommRing A] [CommRing B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (g : A →+* B) (hpq : p = q.comap g)
    (x : A) :
    completionComparison p q g hpq (toCompletion p x) = toCompletion q (g x) := by
  have h : toCompletion p x = ofLocalization p (algebraMap A (Localization.AtPrime p) x) := rfl
  rw [h, completionComparison_ofLocalization, Localization.localRingHom_to_map]
  rfl

/-- The comparison map of completed local rings is local: it carries the maximal ideal into the
maximal ideal. -/
theorem completionComparison_mem_maximalIdeal {A B : Type u} [CommRing A] [CommRing B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (g : A →+* B) (hpq : p = q.comap g)
    [IsNoetherianRing (Localization.AtPrime p)] [IsNoetherianRing (Localization.AtPrime q)]
    {x : Completion p} (hx : x ∈ maximalIdeal (Completion p)) :
    completionComparison p q g hpq x ∈ maximalIdeal (Completion q) := by
  have hle : Ideal.map (completionComparison p q g hpq)
      (Ideal.map (ofLocalization p) (maximalIdeal (Localization.AtPrime p))) ≤
      Ideal.map (ofLocalization q) (maximalIdeal (Localization.AtPrime q)) := by
    have hcomp : (completionComparison p q g hpq).comp (ofLocalization p) =
        (ofLocalization q).comp (Localization.localRingHom p q g hpq) :=
      RingHom.ext fun y => completionComparison_ofLocalization p q g hpq y
    rw [Ideal.map_map, hcomp, ← Ideal.map_map]
    refine Ideal.map_mono ?_
    let := Localization.isLocalHom_localRingHom p q g hpq
    exact IsLocalRing.map_maximalIdeal_le (Localization.localRingHom p q g hpq)
  rw [AdicCompletion.maximalIdeal_eq_map] at hx ⊢
  exact hle (Ideal.mem_map_of_mem _ hx)

/-! ### Agreement of two maps modulo an ideal

Both statements this section used to prove are in the base module
`StacksFrontier/AlgebraicGeometry/Morphisms/EtaleNeighbourhood/ArtinApproximation.lean`, as
`AlgebraicGeometry.agreement_mod_ideal_of_algebra_generators` and
`AlgebraicGeometry.agreement_mod_ideal_of_localization`. The copies that stood here, named
`agreement_of_generators` and `agreement_of_localization`, had the same statements
argument-for-argument and only stylistically different proofs; they are deleted and the two
consumers below use the base declarations. -/

/-! ### The approximation property for G-rings, as an assumed input -/

/-- The data that Artin approximation for G-rings produces: an étale algebra `A'` over `A`, a
prime `𝔭'` of `A'` contracting to `𝔭` with the same residue field, and a solution of the
polynomial system `f` in `A'` which agrees with the given solution `a` over the completion
modulo the `N`-th power of the maximal ideal. -/
structure EtaleSolution (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime]
    {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) A) (N : ℕ)
    (a : Fin n → Completion p) where
  /-- The étale extension of `A`. -/
  carrier : Type u
  /-- Its ring structure. -/
  [commRing : CommRing carrier]
  /-- Its algebra structure over `A`. -/
  [algebra : Algebra A carrier]
  /-- It is étale over `A`. -/
  [etale : Algebra.Etale A carrier]
  /-- The chosen prime of the étale extension. -/
  prime : Ideal carrier
  /-- It is prime. -/
  [isPrime : prime.IsPrime]
  /-- It contracts to the given prime of `A`. -/
  comap_prime : p = prime.comap (algebraMap A carrier)
  /-- The residue field extension is trivial. -/
  residueField_bijective :
    Function.Bijective (Ideal.ResidueField.map p prime (algebraMap A carrier) comap_prime)
  /-- The solution of the polynomial system in the étale extension. -/
  sol : Fin n → carrier
  /-- It is a solution. -/
  eval_sol : ∀ j, MvPolynomial.eval₂ (algebraMap A carrier) sol (f j) = 0
  /-- It approximates the given solution to order `N`. -/
  approx : ∀ i,
    completionComparison p prime (algebraMap A carrier) comap_prime (a i) -
      toCompletion prime (sol i) ∈ completionIdeal prime N

attribute [instance] EtaleSolution.commRing EtaleSolution.algebra EtaleSolution.etale
  EtaleSolution.isPrime

/-- **Stacks 0CAR (Smoothing Ring Maps, Lemma 16.13.4).** Let `A` be a Noetherian ring, let `𝔭`
be a prime of `A` such that `A_𝔭` is a G-ring, and let `f₁, …, f_m` be polynomials over `A` in
`n` variables. If the system `f = 0` has a solution in the completion of `A_𝔭`, then for every
`N` it has a solution in an étale extension `A → A'` at a prime `𝔭'` over `𝔭` with the same
residue field, which agrees with the given solution modulo `𝔪_{𝔭'}^N`.

This is the approximation property of G-rings, whose proof in the source rests on Popescu's
theorem (Stacks 07GC) through Theorem 16.13.2 (Stacks 07QZ). Neither is available in this
development, so it is assumed here as a single explicit hypothesis, in the same way that
`Card_aux_0795.Popescu07GC` assumes Popescu's theorem. -/
def ArtinApproximationGRing : Prop :=
  ∀ (A : Type u) [CommRing A] (p : Ideal A) [p.IsPrime], IsNoetherianRing A →
    IsGRing (Localization.AtPrime p) →
    ∀ (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) A) (N : ℕ) (a : Fin n → Completion p),
      (∀ j, MvPolynomial.eval₂ (toCompletion p) a (f j) = 0) →
      Nonempty (EtaleSolution A p f N a)

/-! ### The affine case of the approximation of a formal map by an actual map -/

/-- The data produced by the affine case of Stacks 0CAU: an elementary étale extension `A'` of
`A` at a prime `𝔭'` over `𝔭`, together with an `R`-algebra map `B → A'` carrying `𝔭'` back to
`𝔮`, whose induced map of local rings agrees with the given `φ` modulo `𝔪_{𝔭'}^N`. -/
structure EtaleApproximation (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (N : ℕ)
    (φ : Localization.AtPrime q →+* Completion p) where
  /-- The étale extension of `A`. -/
  carrier : Type u
  /-- Its ring structure. -/
  [commRing : CommRing carrier]
  /-- Its algebra structure over `A`. -/
  [algebra : Algebra A carrier]
  /-- It is étale over `A`. -/
  [etale : Algebra.Etale A carrier]
  /-- The chosen prime of the étale extension. -/
  prime : Ideal carrier
  /-- It is prime. -/
  [isPrime : prime.IsPrime]
  /-- It contracts to the given prime of `A`. -/
  comap_prime : p = prime.comap (algebraMap A carrier)
  /-- The residue field extension is trivial: the neighbourhood is elementary. -/
  residueField_bijective :
    Function.Bijective (Ideal.ResidueField.map p prime (algebraMap A carrier) comap_prime)
  /-- The map `B → A'`. -/
  toCarrier : B →+* carrier
  /-- It is a map of `R`-algebras. -/
  toCarrier_base :
    toCarrier.comp (algebraMap R B) = (algebraMap A carrier).comp (algebraMap R A)
  /-- It carries the chosen prime of the étale extension back to the given prime of `B`. -/
  comap_toCarrier : q = prime.comap toCarrier
  /-- The induced map of local rings agrees with `φ` modulo the `N`-th power of the maximal
  ideal. -/
  agree : ∀ z : Localization.AtPrime q,
    completionComparison p prime (algebraMap A carrier) comap_prime (φ z) -
      ofLocalization prime (Localization.localRingHom q prime toCarrier comap_toCarrier z) ∈
      completionIdeal prime N

attribute [instance] EtaleApproximation.commRing EtaleApproximation.algebra
  EtaleApproximation.etale EtaleApproximation.isPrime

/-- **The affine case of Stacks 0CAU, conditional on Stacks 0CAR.** Let `R` be a Noetherian
ring, let `A` be a Noetherian `R`-algebra, let `B` be an `R`-algebra of finite type, let
`𝔭 ⊂ A` and `𝔮 ⊂ B` be primes, and
suppose `A_𝔭` is a G-ring. A local `R`-algebra map `φ : B_𝔮 → (A_𝔭)^∧` is approximated, to any
prescribed order `N ≥ 1`, by an actual `R`-algebra map `B → A'` into an étale extension of `A`
at a prime over `𝔭` with the same residue field.

This is the ring-theoretic content of Stacks 37.39.1: `A'` is the coordinate ring of the
elementary étale neighbourhood and `B → A'` is the morphism to `Y`. The hypothesis `hCAR` is
the approximation property for G-rings (Stacks 0CAR); everything else is proved here.

Of `A` only Noetherianness is assumed, not finite type over `R`: `A` enters the proof solely
through the system of equations that Stacks 0CAR is applied to, and 0CAR asks for a Noetherian
ring with a G-ring localization. That is the form the proof of Stacks 0CAW needs at its first
step, where the ring to be extended étale is `B ⊗_{C, σ} R^∧` — Noetherian, being of finite type
over the Noetherian ring `R^∧`, but not of finite type over `R`. -/
theorem exists_etaleApproximation (hCAR : ArtinApproximationGRing.{u})
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsNoetherianRing R] [IsNoetherianRing A] [Algebra.FiniteType R B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hG : IsGRing (Localization.AtPrime p)) (N : ℕ) (hN : 1 ≤ N)
    (φ : Localization.AtPrime q →+* Completion p) (hφ : IsLocalHom φ)
    (hbase : φ.comp ((algebraMap B (Localization.AtPrime q)).comp (algebraMap R B)) =
      (toCompletion p).comp (algebraMap R A)) :
    Nonempty (EtaleApproximation R A B p q N φ) := by
  classical
  have hAnoeth : IsNoetherianRing A := inferInstance
  have hpnoeth : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl (Localization.AtPrime p) hAnoeth
  have hφ' : IsLocalHom φ := hφ
  -- A finite presentation `B = R[x₁, …, x_n] / (F₁, …, F_m)` of `B` over `R`.
  obtain ⟨n, π, hπsurj, hπfg⟩ :=
    ((Algebra.FinitePresentation.of_finiteType (R := R) (A := B)).mp inferInstance).out
  obtain ⟨m, F, hF⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hπfg
  have hkerF : ∀ j, π (F j) = 0 := by
    intro j
    have hmem : F j ∈ RingHom.ker π.toRingHom := by
      rw [← hF]; exact Submodule.subset_span ⟨j, rfl⟩
    exact hmem
  have hπC : ∀ r : R, π (MvPolynomial.C r) = algebraMap R B r := fun r => by
    rw [← MvPolynomial.algebraMap_eq]; exact π.commutes r
  -- The system of equations over `A`, and the solution of it in the completion.
  let a : Fin n → Completion p := fun i =>
    φ (algebraMap B (Localization.AtPrime q) (π (MvPolynomial.X i)))
  let g : Fin m → MvPolynomial (Fin n) A := fun j => MvPolynomial.map (algebraMap R A) (F j)
  let Θ : MvPolynomial (Fin n) R →+* Completion p :=
    (φ.comp (algebraMap B (Localization.AtPrime q))).comp π.toRingHom
  have hΘ : Θ = MvPolynomial.eval₂Hom ((toCompletion p).comp (algebraMap R A)) a := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun i => ?_)
    · simp only [Θ, RingHom.coe_comp, Function.comp_apply, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, hπC, MvPolynomial.eval₂Hom_C]
      exact RingHom.congr_fun hbase r
    · simp [Θ, a]
  have hΘ' : ∀ P : MvPolynomial (Fin n) R,
      Θ P = MvPolynomial.eval₂ ((toCompletion p).comp (algebraMap R A)) a P := by
    intro P; rw [hΘ]; rfl
  have heval : ∀ j, MvPolynomial.eval₂ (toCompletion p) a (g j) = 0 := by
    intro j
    calc MvPolynomial.eval₂ (toCompletion p) a (g j)
        = MvPolynomial.eval₂ ((toCompletion p).comp (algebraMap R A)) a (F j) :=
          MvPolynomial.eval₂_map _ _ _ _
      _ = Θ (F j) := (hΘ' (F j)).symm
      _ = 0 := by simp only [Θ, RingHom.coe_comp, Function.comp_apply,
          AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hkerF j, _root_.map_zero]
  -- Artin approximation for the G-ring `A_𝔭` applied to this system.
  obtain ⟨A', p', hcp, hres, sol, hsol, happrox⟩ := hCAR A p hAnoeth hG n m g N a heval
  have hA'noeth : IsNoetherianRing A' := Algebra.FiniteType.isNoetherianRing A A'
  have hp'noeth : IsNoetherianRing (Localization.AtPrime p') :=
    IsLocalization.isNoetherianRing p'.primeCompl (Localization.AtPrime p') hA'noeth
  let : Algebra R A' := ((algebraMap A A').comp (algebraMap R A)).toAlgebra
  have htower : IsScalarTower R A A' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  let := htower
  -- The `R`-algebra map `B → A'` determined by the solution.
  let ψ₀ : MvPolynomial (Fin n) R →ₐ[R] A' := MvPolynomial.aeval sol
  have hψ₀ : ∀ j, ψ₀ (F j) = 0 := by
    intro j
    have h : ψ₀ (F j) = MvPolynomial.eval₂ (algebraMap A A') sol (g j) := by
      have h1 : ψ₀ (F j) =
          MvPolynomial.eval₂ ((algebraMap A A').comp (algebraMap R A)) sol (F j) := rfl
      rw [h1, ← MvPolynomial.eval₂_map]
    rw [h]; exact hsol j
  have hkerle : RingHom.ker π.toRingHom ≤ RingHom.ker ψ₀.toRingHom := by
    rw [← hF]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨j, rfl⟩
    exact hψ₀ j
  obtain ⟨ψ, hψπ⟩ : ∃ ψ : B →+* A', ∀ x, ψ (π x) = ψ₀ x :=
    ⟨RingHom.liftOfSurjective π.toRingHom hπsurj ⟨ψ₀.toRingHom, hkerle⟩,
      fun x => RingHom.liftOfSurjective_comp_apply π.toRingHom hπsurj
        ⟨ψ₀.toRingHom, hkerle⟩ x⟩
  have hψbase : ∀ r : R, ψ (algebraMap R B r) = algebraMap A A' (algebraMap R A r) := by
    intro r
    rw [← hπC, hψπ]
    simp only [ψ₀, MvPolynomial.aeval_C]
    rfl
  -- The two maps `B → (A'_{𝔭'})^∧` to be compared.
  let cc : Completion p →+* Completion p' := completionComparison p p' (algebraMap A A') hcp
  let Φ : B →+* Completion p' := cc.comp (φ.comp (algebraMap B (Localization.AtPrime q)))
  let Ψ : B →+* Completion p' := (toCompletion p').comp ψ
  let K : Ideal (Completion p') := completionIdeal p' N
  have hΦbase : ∀ r : R, Φ (algebraMap R B r) = Ψ (algebraMap R B r) := by
    intro r
    have h1 : Φ (algebraMap R B r) = cc (toCompletion p (algebraMap R A r)) := by
      simp only [Φ, RingHom.coe_comp, Function.comp_apply]
      exact congrArg cc (RingHom.congr_fun hbase r)
    have h2 : cc (toCompletion p (algebraMap R A r)) =
        toCompletion p' (algebraMap A A' (algebraMap R A r)) :=
      completionComparison_toCompletion p p' (algebraMap A A') hcp _
    calc Φ (algebraMap R B r) = cc (toCompletion p (algebraMap R A r)) := h1
      _ = toCompletion p' (algebraMap A A' (algebraMap R A r)) := h2
      _ = toCompletion p' (ψ (algebraMap R B r)) := by rw [hψbase r]
      _ = Ψ (algebraMap R B r) := rfl
  let : Algebra R (Completion p') := (Ψ.comp (algebraMap R B)).toAlgebra
  let ΨA : B →ₐ[R] Completion p' := { toRingHom := Ψ, commutes' := fun _ => rfl }
  let ΦA : B →ₐ[R] Completion p' := { toRingHom := Φ, commutes' := hΦbase }
  have hgens : Algebra.adjoin R (Set.range fun i => π (MvPolynomial.X i)) = ⊤ := by
    have h1 : (Set.range fun i => π (MvPolynomial.X i)) =
        π '' Set.range (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R) := by
      rw [← Set.range_comp]; rfl
    rw [h1, Algebra.adjoin_image, MvPolynomial.adjoin_range_X, Algebra.map_top]
    exact (AlgHom.range_eq_top π).mpr hπsurj
  have hagreeB : ∀ b : B, Φ b - Ψ b ∈ K := by
    refine AlgebraicGeometry.agreement_mod_ideal_of_algebra_generators K ΦA ΨA _ hgens ?_
    rintro _ ⟨i, rfl⟩
    have hΦi : ΦA (π (MvPolynomial.X i)) = cc (a i) := rfl
    have hΨi : ΨA (π (MvPolynomial.X i)) = toCompletion p' (sol i) := by
      have h1 : ΨA (π (MvPolynomial.X i)) = toCompletion p' (ψ (π (MvPolynomial.X i))) := rfl
      rw [h1, hψπ]
      simp only [ψ₀, MvPolynomial.aeval_X]
    rw [hΦi, hΨi]
    exact happrox i
  -- `K` sits inside the maximal ideal, which is where `N ≥ 1` is used.
  have hKle : K ≤ maximalIdeal (Completion p') := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact Ideal.map_mono (Ideal.pow_le_self (by omega))
  -- The map `B → A'` carries `𝔭'` back to `𝔮`.
  have hcq : q = p'.comap ψ := by
    refine le_antisymm (fun b hb => ?_) (fun b hb => ?_)
    · -- `b ∈ 𝔮` forces `ψ b ∈ 𝔭'`.
      have h1 : algebraMap B (Localization.AtPrime q) b ∈
          maximalIdeal (Localization.AtPrime q) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q b).mpr hb
      have h1u : ¬ IsUnit (algebraMap B (Localization.AtPrime q) b) := fun hu =>
        IsLocalRing.notMem_maximalIdeal.mpr hu h1
      have h2 : φ (algebraMap B (Localization.AtPrime q) b) ∈ maximalIdeal (Completion p) := by
        by_contra hc
        exact h1u (hφ'.map_nonunit _ (IsLocalRing.notMem_maximalIdeal.mp hc))
      have h3 : Φ b ∈ maximalIdeal (Completion p') :=
        completionComparison_mem_maximalIdeal p p' (algebraMap A A') hcp h2
      have h4 : Ψ b ∈ maximalIdeal (Completion p') := by
        have := sub_mem h3 (hKle (hagreeB b))
        simpa using this
      have h5 : ¬ IsUnit (algebraMap A' (Localization.AtPrime p') (ψ b)) := by
        intro hu
        exact IsLocalRing.notMem_maximalIdeal.mpr (hu.map (ofLocalization p')) h4
      have h6 : ψ b ∉ p'.primeCompl := fun hmem =>
        h5 ((IsLocalization.AtPrime.isUnit_to_map_iff _ p' (ψ b)).mpr hmem)
      exact Ideal.mem_comap.mpr (not_not.mp h6)
    · -- Conversely, `ψ b ∈ 𝔭'` forces `b ∈ 𝔮`.
      by_contra hbq
      have h1 : IsUnit (algebraMap B (Localization.AtPrime q) b) :=
        (IsLocalization.AtPrime.isUnit_to_map_iff _ q b).mpr hbq
      have h2 : IsUnit (Φ b) := (h1.map φ).map cc
      have h3 : Ψ b ∉ maximalIdeal (Completion p') := by
        intro hmem
        refine IsLocalRing.notMem_maximalIdeal.mpr h2 ?_
        have := add_mem hmem (hKle (hagreeB b))
        simpa using this
      have h4 : IsUnit (algebraMap A' (Localization.AtPrime p') (ψ b)) := by
        have h5 : IsUnit (ofLocalization p' (algebraMap A' (Localization.AtPrime p') (ψ b))) :=
          IsLocalRing.notMem_maximalIdeal.mp h3
        exact (AdicCompletion.algebraMap_isLocalHom_of_fg
          (maximalIdeal (Localization.AtPrime p')).fg_of_isNoetherianRing).map_nonunit _ h5
      have h6 : ψ b ∈ p'.primeCompl :=
        (IsLocalization.AtPrime.isUnit_to_map_iff _ p' (ψ b)).mp h4
      have h7 : ψ b ∉ p' := h6
      exact h7 (Ideal.mem_comap.mp hb)
  -- The agreement of the two maps out of `B_𝔮`.
  have hagree : ∀ z : Localization.AtPrime q,
      cc (φ z) - ofLocalization p' (Localization.localRingHom q p' ψ hcq z) ∈ K := by
    refine AlgebraicGeometry.agreement_mod_ideal_of_localization q.primeCompl K (cc.comp φ)
      ((ofLocalization p').comp (Localization.localRingHom q p' ψ hcq)) ?_
    intro b
    have h1 : ((ofLocalization p').comp
        (Localization.localRingHom q p' ψ hcq)) (algebraMap B _ b) = Ψ b := by
      simp only [RingHom.coe_comp, Function.comp_apply, Localization.localRingHom_to_map]
      rfl
    have h2 : (cc.comp φ) (algebraMap B (Localization.AtPrime q) b) = Φ b := rfl
    rw [h1, h2]
    exact hagreeB b
  exact ⟨{ carrier := A'
           prime := p'
           comap_prime := hcp
           residueField_bijective := hres
           toCarrier := ψ
           toCarrier_base := RingHom.ext hψbase
           comap_toCarrier := hcq
           agree := hagree }⟩

/-! ### The scheme-theoretic reading of the approximation -/

namespace EtaleApproximation

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  {p : Ideal A} [p.IsPrime] {q : Ideal B} [q.IsPrime] {N : ℕ}
  {φ : Localization.AtPrime q →+* Completion p} (E : EtaleApproximation R A B p q N φ)

/-- The structure morphism of the neighbourhood, `Spec A' → Spec A`. -/
noncomputable abbrev specToBase :
    Spec (CommRingCat.of E.carrier) ⟶ Spec (CommRingCat.of A) :=
  Spec.map (CommRingCat.ofHom (algebraMap A E.carrier))

/-- The morphism to `Y`, `Spec A' → Spec B`. -/
noncomputable abbrev specToTarget :
    Spec (CommRingCat.of E.carrier) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom E.toCarrier)

/-- The distinguished point of the neighbourhood. -/
abbrev specPoint : PrimeSpectrum E.carrier := ⟨E.prime, E.isPrime⟩

/-- The structure morphism of the neighbourhood is étale. -/
theorem etale_specToBase : Etale E.specToBase := by
  rw [HasRingHomProperty.Spec_iff (P := @Etale)]
  exact RingHom.etale_algebraMap.mpr E.etale

/-- The distinguished point lies over `x = 𝔭`. -/
theorem specToBase_specPoint :
    E.specToBase E.specPoint = (⟨p, inferInstance⟩ : PrimeSpectrum A) :=
  PrimeSpectrum.ext E.comap_prime.symm

/-- The morphism to `Y` carries the distinguished point to `y = 𝔮`. -/
theorem specToTarget_specPoint :
    E.specToTarget E.specPoint = (⟨q, inferInstance⟩ : PrimeSpectrum B) :=
  PrimeSpectrum.ext E.comap_toCarrier.symm

/-- The morphism to `Y` is a morphism over the base `Spec R`. -/
theorem specToTarget_over :
    E.specToTarget ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) =
      E.specToBase ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) := by
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext E.toCarrier_base

end EtaleApproximation

/-! ### The G-ring hypothesis of the source -/

/-- **Stacks 07PV at a prime.** If the local ring of `R` at the prime under `𝔭` is a G-ring and
`A` is of finite type over `R`, then the local ring of `A` at `𝔭` is a G-ring: it is essentially
of finite type over the former. This is the step by which Stacks 37.39.1 passes from its
hypothesis that `𝒪_{S,s}` is a G-ring to the hypothesis that Stacks 0CAR needs. -/
theorem isGRing_localization_atPrime {R A : Type u} [CommRing R] [CommRing A] [Algebra R A]
    [Algebra.FiniteType R A] (p : Ideal A) [p.IsPrime]
    (hG : IsGRing (Localization.AtPrime (p.under R))) :
    IsGRing (Localization.AtPrime p) := by
  let : Algebra (Localization.AtPrime (p.under R)) (Localization.AtPrime p) :=
    Localization.AtPrime.algebraOfLiesOver (p.under R) p
  have : IsScalarTower R (Localization.AtPrime (p.under R)) (Localization.AtPrime p) :=
    inferInstance
  have h1 : Algebra.EssFiniteType R (Localization.AtPrime p) :=
    Algebra.EssFiniteType.comp R A (Localization.AtPrime p)
  have h2 : Algebra.EssFiniteType (Localization.AtPrime (p.under R)) (Localization.AtPrime p) :=
    Algebra.EssFiniteType.of_comp R _ _
  exact isGRing_of_essFiniteType hG

/-- **The affine case of Stacks 0CAU, conditional on Stacks 0CAR, with the source's own G-ring
hypothesis.** The assumption is that the local ring of the base `R` at the image prime is a
G-ring — in the geometric statement, that `𝒪_{S,s}` is a G-ring. -/
theorem exists_etaleApproximation_of_isGRing_base (hCAR : ArtinApproximationGRing.{u})
    {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsNoetherianRing R] [Algebra.FiniteType R A] [Algebra.FiniteType R B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime]
    (hG : IsGRing (Localization.AtPrime (p.under R))) (N : ℕ) (hN : 1 ≤ N)
    (φ : Localization.AtPrime q →+* Completion p) (hφ : IsLocalHom φ)
    (hbase : φ.comp ((algebraMap B (Localization.AtPrime q)).comp (algebraMap R B)) =
      (toCompletion p).comp (algebraMap R A)) :
    Nonempty (EtaleApproximation R A B p q N φ) :=
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing R A
  exists_etaleApproximation hCAR p q (isGRing_localization_atPrime p hG) N hN φ hφ hbase

end StacksDraft.ArtinApproximation

end
