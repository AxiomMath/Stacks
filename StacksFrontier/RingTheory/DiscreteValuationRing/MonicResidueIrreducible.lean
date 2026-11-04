module

public import Mathlib.RingTheory.Polynomial.GaussLemma
public import StacksFrontier.RingTheory.AdjoinRoot.LocalRing
public import StacksFrontier.RingTheory.DiscreteValuationRing.Unramified
public import StacksFrontier.RingTheory.DiscreteValuationRing.WeakSolutionObstruction
public import StacksFrontier.RingTheory.DiscreteValuationRing.FundamentalIdentity
public import StacksFrontier.RingTheory.DiscreteValuationRing.HenselianDegreeFormula

/-!
# Adjoining a root of a polynomial with irreducible residue reduction to a discrete valuation ring

Let `A` be a discrete valuation ring with fraction field `K` and residue field `κ`, and let
`p ∈ A[X]` be monic of degree `n ≥ 1` whose reduction `p̄ ∈ κ[X]` is irreducible.  Then

* `p` is irreducible over `A` and over `K`, so `K[X] ⧸ (p)` is a degree-`n` field extension;
* `B = A[X] ⧸ (p)` is again a discrete valuation ring, and every uniformizer of `A` stays a
  uniformizer of `B`, i.e. the ramification index is `e = 1`;
* the residue degree is `f = n`, and the residue of the adjoined root is a root of `p̄`.

This is the general mechanism behind "the equation is irreducible modulo the uniformizer, so the
extension is unramified and the whole degree goes into the residue field".  A typical instance
is the transformed Artin--Schreier equation, whose reduction is `w̄ ^ 2 = b / a`, irreducible
because `b / a` is not a square in the residue field.

It is also the general form of Stacks Tag 09EX
(`StacksFrontier.RingTheory.DiscreteValuationRing.AdjoinPthRoot`), which is the case
`p = X ^ q - C a` with `a` a non-`q`-th power residue: there the reduction `X ^ q - C ā` is
irreducible for exactly that reason.  The two files are stated over different models of the
extension — 09EX inside a chosen splitting field `K[a^{1/q}]`, this one as `AdjoinRoot p` itself —
so neither is literally an instance of the other; the shared local algebra lives in
`StacksFrontier.RingTheory.AdjoinRoot.LocalRing`.

## Main results

* `Stacks.DiscreteValuationRing.Ramification.inertiaDeg_eq_finrank_residueField`: for a local
  homomorphism of local rings the
  ideal-theoretic residue degree is the degree of the residue field extension.  This is the
  quantity called `δ` in the note.
* `AdjoinRoot.irreducible_of_irreducible_map_residue`,
  `AdjoinRoot.irreducible_map_algebraMap_of_irreducible_map_residue`: irreducibility of `p` over
  `A` and over `K` — *irreducibility modulo the uniformizer implies irreducibility*.
* `AdjoinRoot.isDomain_of_irreducible_map_residue`, `AdjoinRoot.isDiscreteValuationRing`: the
  monogenic algebra is a discrete valuation ring.
* `AdjoinRoot.maximalIdeal_eq_span_algebraMap`, `AdjoinRoot.irreducible_algebraMap`,
  `AdjoinRoot.ramificationIdx_eq_one`: the extension is weakly unramified, `e = 1`.
* `AdjoinRoot.inertiaDeg_eq_natDegree`, `AdjoinRoot.finrank_residueField_eq_natDegree`: the
  residue degree is `n = deg p`.
* `AdjoinRoot.eval₂_residue_root_eq_zero`: the residue of the adjoined root is a root of `p̄`.

## References

* [The Stacks Project, Tag 09E4](https://stacks.math.columbia.edu/tag/09E4)
* [The Stacks Project, Tag 09EX](https://stacks.math.columbia.edu/tag/09EX)
-/

@[expose] public section

open IsLocalRing Polynomial

namespace Stacks.DiscreteValuationRing.Ramification

/-- **The residue degree of a local extension is the degree of the residue field extension.**

`Ideal.inertiaDeg` is defined through the residue field of a localization; for a local ring map
between local rings the maximal ideal upstairs already lies over the maximal ideal downstairs, so
the localizations are redundant and the residue degree is the plain degree
`[κ_B : κ_A]`. -/
theorem inertiaDeg_eq_finrank_residueField (A B : Type*) [CommRing A] [IsLocalRing A] [CommRing B]
    [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)] :
    Ideal.inertiaDeg (maximalIdeal B) A = Module.finrank (ResidueField A) (ResidueField B) := by
  rw [Ideal.inertiaDeg_eq_of_isMaximal (p := maximalIdeal A)]
  rfl

end Stacks.DiscreteValuationRing.Ramification

namespace AdjoinRoot

variable {A : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] {p : A[X]}

/-! ### Irreducibility from irreducibility of the reduction -/

/-- **Irreducible modulo the maximal ideal implies irreducible.** A monic polynomial over a
commutative domain whose reduction modulo the maximal ideal of a local ring is irreducible is
itself irreducible: a factorization into monic factors would reduce to one. -/
theorem irreducible_of_irreducible_map_residue (hp : p.Monic)
    (hirr : Irreducible (p.map (residue A))) : Irreducible p :=
  Polynomial.Monic.irreducible_of_irreducible_map (residue A) p hp hirr

/-- A discrete valuation ring is a unique factorization domain, so the irreducible `p` is prime. -/
theorem prime_of_irreducible_map_residue (hp : p.Monic)
    (hirr : Irreducible (p.map (residue A))) : Prime p :=
  UniqueFactorizationMonoid.irreducible_iff_prime.mp
    (irreducible_of_irreducible_map_residue hp hirr)

/-- **Irreducibility over the fraction field.** Gauss's lemma for the integrally closed ring `A`
turns irreducibility of the monic `p` over `A` into irreducibility over `K`; so `K[X] ⧸ (p)` is a
field extension of `K` of degree `deg p`. -/
theorem irreducible_map_algebraMap_of_irreducible_map_residue {K : Type*} [Field K] [Algebra A K]
    [IsFractionRing A K] (hp : p.Monic) (hirr : Irreducible (p.map (residue A))) :
    Irreducible (p.map (algebraMap A K)) :=
  (hp.irreducible_iff_irreducible_map_fraction_map (K := K)).mp
    (irreducible_of_irreducible_map_residue hp hirr)

/-- `A[X] ⧸ (p)` is a domain, `p` being prime. -/
theorem isDomain_of_irreducible_map_residue (hp : p.Monic)
    (hirr : Irreducible (p.map (residue A))) : IsDomain (AdjoinRoot p) :=
  AdjoinRoot.isDomain_of_prime (prime_of_irreducible_map_residue hp hirr)

/-! ### Freeness and the degree -/

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- `A[X] ⧸ (p)` is free over `A` on the power basis of the adjoined root. -/
theorem free_of_monic (hp : p.Monic) : Module.Free A (AdjoinRoot p) :=
  Module.Free.of_basis (AdjoinRoot.powerBasis' hp).basis

omit [IsDiscreteValuationRing A] in
/-- The rank of `A[X] ⧸ (p)` over `A` is the degree of `p`. -/
theorem finrank_eq_natDegree (hp : p.Monic) :
    Module.finrank A (AdjoinRoot p) = p.natDegree := by
  rw [(AdjoinRoot.powerBasis' hp).finrank, AdjoinRoot.powerBasis'_dim]

/-! ### The discrete valuation ring structure, and `e = 1` -/

section Local

variable [IsLocalRing (AdjoinRoot p)]

/-- **The maximal ideal of `A[X] ⧸ (p)` is generated by a uniformizer of `A`.** This is
unramifiedness: nothing has been added to the maximal ideal. -/
theorem maximalIdeal_eq_span_algebraMap (hirr : Irreducible (p.map (residue A))) {π : A}
    (hπ : Irreducible π) :
    maximalIdeal (AdjoinRoot p) = Ideal.span {algebraMap A (AdjoinRoot p) π} := by
  rw [maximalIdeal_eq_map_maximalIdeal hirr,
    (IsDiscreteValuationRing.irreducible_iff_uniformizer π).mp hπ, Ideal.map_span,
    Set.image_singleton, AdjoinRoot.algebraMap_eq]

variable [IsDomain (AdjoinRoot p)]

/-- **`A[X] ⧸ (p)` is a discrete valuation ring.** It is a Noetherian local domain whose maximal
ideal is generated by the image of a uniformizer of `A`. -/
theorem isDiscreteValuationRing (hp : p.Monic) (hirr : Irreducible (p.map (residue A)))
    (hd : 0 < p.natDegree) : IsDiscreteValuationRing (AdjoinRoot p) := by
  have : Module.Finite A (AdjoinRoot p) := hp.finite_adjoinRoot
  have : IsNoetherianRing (AdjoinRoot p) := IsNoetherianRing.of_finite A (AdjoinRoot p)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hne : algebraMap A (AdjoinRoot p) π ≠ 0 := fun h =>
    hπ.ne_zero (of.injective_of_monic_of_degree_pos hp
      (natDegree_pos_iff_degree_pos.mp hd) (by simpa using h))
  exact (IsLocalRing.isDiscreteValuationRing_of_maximalIdeal_eq_span
    (maximalIdeal_eq_span_algebraMap hirr hπ) fun _ _ => mul_left_cancel₀ hne).2.1

/-- **Every uniformizer of `A` stays a uniformizer.** This is weak unramifiedness in the sense of
Stacks Tag 09E4. -/
theorem irreducible_algebraMap (hp : p.Monic) (hirr : Irreducible (p.map (residue A)))
    (hd : 0 < p.natDegree) {π : A} (hπ : Irreducible π) :
    Irreducible (algebraMap A (AdjoinRoot p) π) := by
  have := isDiscreteValuationRing hp hirr hd
  exact (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mpr
    (maximalIdeal_eq_span_algebraMap hirr hπ)

/-- **The ramification index is one.** -/
theorem ramificationIdx_eq_one (hp : p.Monic) (hirr : Irreducible (p.map (residue A)))
    (hd : 0 < p.natDegree) :
    Stacks.DiscreteValuationRing.Ramification.ramificationIdx A (AdjoinRoot p) = 1 := by
  have hdvr := isDiscreteValuationRing hp hirr hd
  have hfs := faithfulSMul_of_monic_of_degree_pos hp (natDegree_pos_iff_degree_pos.mp hd)
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible A
  have hval := Stacks.DiscreteValuationRing.Ramification.addVal_algebraMap_eq_ramificationIdx A
    (AdjoinRoot p) π hπ
  rw [IsDiscreteValuationRing.addVal_uniformizer
    (irreducible_algebraMap hp hirr hd hπ)] at hval
  exact_mod_cast hval.symm

/-! ### The residue degree, and the residue of the adjoined root -/

/-- **The residue degree is the degree of `p`.** With `e = 1` the local fundamental identity
`[Frac B : K] = e f` puts the whole degree of `p` into the residue field. -/
theorem inertiaDeg_eq_natDegree (hp : p.Monic) (hirr : Irreducible (p.map (residue A)))
    (hd : 0 < p.natDegree) :
    Ideal.inertiaDeg (maximalIdeal (AdjoinRoot p)) A = p.natDegree := by
  have hdvr := isDiscreteValuationRing hp hirr hd
  have hfs := faithfulSMul_of_monic_of_degree_pos hp (natDegree_pos_iff_degree_pos.mp hd)
  have hfin : Module.Finite A (AdjoinRoot p) := hp.finite_adjoinRoot
  have hfree := free_of_monic (p := p) hp
  have hflat : Module.Flat A (AdjoinRoot p) := Module.Flat.of_free
  have hlh : IsLocalHom (algebraMap A (AdjoinRoot p)) := by
    rw [AdjoinRoot.algebraMap_eq]
    exact isLocalHom_of_monic hp
  -- Put the extension inside the fraction fields of `A` and of `AdjoinRoot p`.
  have : FaithfulSMul A (FractionRing (AdjoinRoot p)) :=
    (faithfulSMul_iff_algebraMap_injective _ _).mpr <| by
      rw [IsScalarTower.algebraMap_eq A (AdjoinRoot p) (FractionRing (AdjoinRoot p))]
      exact (IsFractionRing.injective (AdjoinRoot p) (FractionRing (AdjoinRoot p))).comp
        (of.injective_of_monic_of_degree_pos hp (natDegree_pos_iff_degree_pos.mp hd))
  let _ : Algebra (FractionRing A) (FractionRing (AdjoinRoot p)) :=
    FractionRing.liftAlgebra A (FractionRing (AdjoinRoot p))
  have : IsScalarTower A (FractionRing A) (FractionRing (AdjoinRoot p)) :=
    FractionRing.isScalarTower_liftAlgebra A (FractionRing (AdjoinRoot p))
  have hfund := Stacks.DiscreteValuationRing.Ramification.ramificationIdx_mul_inertiaDeg_eq_finrank
    A (AdjoinRoot p)
    (FractionRing A) (FractionRing (AdjoinRoot p))
  rwa [ramificationIdx_eq_one hp hirr hd, one_mul,
    IsFractionRing.finrank_eq A (FractionRing A) (AdjoinRoot p) (FractionRing (AdjoinRoot p)),
    finrank_eq_natDegree hp] at hfund

/-- The residue field extension has degree `deg p`.

This is the residue degree of the step `AdjoinRoot p / A`.  The `IsLocalHom` instance, which is
what gives the residue fields their
algebra structure, is supplied by `AdjoinRoot.isLocalHom_of_monic`. -/
theorem finrank_residueField_eq_natDegree [IsLocalHom (algebraMap A (AdjoinRoot p))]
    (hp : p.Monic) (hirr : Irreducible (p.map (residue A))) (hd : 0 < p.natDegree) :
    Module.finrank (ResidueField A) (ResidueField (AdjoinRoot p)) = p.natDegree :=
  (Stacks.DiscreteValuationRing.Ramification.inertiaDeg_eq_finrank_residueField A
    (AdjoinRoot p)).symm.trans (inertiaDeg_eq_natDegree hp hirr hd)

end Local

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- **The residue of the adjoined root is a root of the reduction `p̄`.** This is the statement
that the residue field extension realizes the root of `p̄`: it is just the defining equation of
`AdjoinRoot p` pushed through the residue map. -/
theorem eval₂_residue_root_eq_zero [IsLocalRing (AdjoinRoot p)] :
    Polynomial.eval₂
        ((residue (AdjoinRoot p)).comp (algebraMap A (AdjoinRoot p)))
        (residue (AdjoinRoot p) (AdjoinRoot.root p)) p = 0 := by
  rw [← Polynomial.hom_eval₂ p (algebraMap A (AdjoinRoot p)) (residue (AdjoinRoot p))
    (AdjoinRoot.root p), ← Polynomial.aeval_def, AdjoinRoot.aeval_eq, AdjoinRoot.mk_self,
    map_zero]

end AdjoinRoot
