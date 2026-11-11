module

public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.SurjectiveOnStalks
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.EtaleNeighbourhood.FiberLifting
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.ArtinApproximationMorphism
public import StacksFrontier.RingTheory.Smoothing.ApproximationGRing
public import StacksCore.Tactic.StacksAttribute

/-!
# The approximation property for G-rings

Let `A` be a Noetherian ring, let `𝔭 ⊂ A` be a prime such that `A_𝔭` is a G-ring, and let
`f₁, …, f_m` be polynomials in `n` variables over `A`. If the system `f = 0` has a solution in
`(A_𝔭)^∧`, then for every `N` it has a solution in an étale extension `A → A'` at a prime `𝔭'`
over `𝔭` with the same residue field, agreeing with the given solution modulo `𝔪_{𝔭'}^N`.

## Main results

* `StacksDraft.ArtinApproximation.artinApproximationGRing`: Stacks 0CAR.
* `StacksDraft.ArtinApproximation.artinApproximationGRing_of_local`: the reduction of 0CAR to its
  own local case (Theorem 07QZ) together with the finite-stage descent of an étale algebra along
  a localization (Algebra, Lemma 00U2 (10)).
* `StacksDraft.ArtinApproximation.localApproximationProperty`: the first of those two inputs,
  which is Theorem 07QZ.
* `StacksDraft.ArtinApproximation.etaleDescentAlongLocalization`: the second of those two inputs,
  proved from `AlgebraicGeometry.exists_etale_pushout_of_localization`.

## Implementation notes

The source's proof of 0CAR has exactly two inputs, and both are proved in this file.

* `LocalApproximationProperty` is **Theorem 07QZ** (Stacks 16.13.2), the same statement for a
  Noetherian local ring, in the exact shape in which 0CAR's proof consumes it: the datum is
  `StacksDraft.ArtinApproximation.LocalEtaleSolution`, produced by Theorem 07QZ
  (`Stacks.Smoothing.exists_localEtaleSolution_of_isGRing`), which also proves the two
  conclusions 07QZ's own statement adds to it — maximality of the distinguished prime, and the
  congruence read in `R^∧`. So this predicate asks only for what 0CAR's proof uses.

  It is proved at the end of this file, as `localApproximationProperty`, from
  `Stacks.Smoothing.exists_localEtaleSolution_of_isGRing`: the route from `IsGRing` to
  `Stacks.Smoothing.IsIndSmoothAdicCompletion R (maximalIdeal R)` is
  `Stacks.Smoothing.isIndSmoothAdicCompletion_of_isGRing`, Popescu's Theorem 07GC
  (`Stacks.Smoothing.indSmooth_of_isRegularRingMap`) together with Lemma 0AH2
  (`Stacks.GRing.isRegularRingHom_algebraMap_adicCompletion`).
* `EtaleDescentAlongLocalization` is **Algebra, Lemma 00U2 (10)**: an étale algebra over a
  localization `M⁻¹A` is the base change of an étale algebra over `A`; equivalently — and this is
  the form used here — it is the localization of an étale `A`-algebra at the image of `M`. This
  is `AlgebraicGeometry.exists_etale_pushout_of_localization`, which states it as a pushout
  square of `CommRingCat`; `etaleDescentAlongLocalization` below turns that square into the
  localization form with `CommRingCat.isPushout_iff_isPushout` and
  `Algebra.isLocalization_iff_isPushout`.

Everything between those two inputs and 0CAR is proved here: the base change of the polynomial
system from `A` to `A_𝔭`, the descent of the solution and of its equations from `A_𝔭 ⊗ E` to a
principal localization of `E` (the source's "after replacing `R'` by a principal localization"),
the identification of the distinguished prime `𝔭'` and of the local ring `E_{𝔭'}` with `S_q`,
the residue field equality `κ(𝔭) = κ(𝔭')`, and the transport of the congruence along that
identification.

The congruence is transported through `AdicCompletion.evalₐ` rather than through the completions
directly: membership in `completionIdeal` is equivalent, for a finitely generated ideal, to dying
in the quotient by the `N`-th power, and that quotient is where the identification of the two
local rings can be computed.

## References

* [Stacks Project, Tag 0CAR](https://stacks.math.columbia.edu/tag/0CAR)
* [Stacks Project, Tag 07QZ](https://stacks.math.columbia.edu/tag/07QZ)
* [Stacks Project, Tag 00U2](https://stacks.math.columbia.edu/tag/00U2)
-/

@[expose] public section

open CategoryTheory IsLocalRing AdicCompletion

universe u

namespace StacksDraft.ArtinApproximation

/-! ### Theorem 07QZ, the local case, as the input of the reduction -/

/-- **Stacks 07QZ (Smoothing Ring Maps, Theorem 16.13.2).** Let `L` be a Noetherian local G-ring
and let `f₁, …, f_m` be polynomials in `n` variables over `L`. If the system `f = 0` has a
solution in the completion of `L`, then for every `N` it has a solution in an étale extension of
`L` at a prime over the maximal ideal with the same residue field, agreeing with the given
solution modulo the `N`-th power of the maximal ideal.

The source proves this from Popescu's theorem (Stacks 07GC). It is named because it is what the
reduction below consumes, and it is proved as
`StacksDraft.ArtinApproximation.localApproximationProperty` at the end of this file; the
embedding into `R^∧` that its conclusion does not mention is supplied by
`StacksDraft.ArtinApproximation.exists_algHom_approx_of_localEtaleSolution`. -/
def LocalApproximationProperty : Prop :=
  ∀ (L : Type u) [CommRing L] [IsLocalRing L], IsNoetherianRing L → IsGRing L →
    ∀ (n m : ℕ) (f : Fin m → MvPolynomial (Fin n) L) (N : ℕ)
      (a : Fin n → AdicCompletion (maximalIdeal L) L),
      (∀ j, MvPolynomial.eval₂ (algebraMap L (AdicCompletion (maximalIdeal L) L)) a (f j) = 0) →
      Nonempty (LocalEtaleSolution L f N a)

/-! ### Algebra, Lemma 00U2 (10), the finite-stage descent, as the input of the reduction -/

/-- The datum that the finite-stage descent of an étale algebra along a localization produces:
an étale `A`-algebra `E` of which `S` is the localization at the image of `M`. -/
structure LocalizationDescent (A : Type u) [CommRing A] (M : Submonoid A) (L : Type u)
    [CommRing L] [Algebra A L] [IsLocalization M L] (S : Type u) [CommRing S] [Algebra L S]
    [Algebra A S] [IsScalarTower A L S] where
  /-- The étale `A`-algebra the étale `L`-algebra descends to. -/
  carrier : Type u
  /-- Its ring structure. -/
  [commRing : CommRing carrier]
  /-- Its algebra structure over `A`. -/
  [algebra : Algebra A carrier]
  /-- It is étale over `A`. -/
  [etale : Algebra.Etale A carrier]
  /-- The map to `S`. -/
  [algebraS : Algebra carrier S]
  /-- It is a map of `A`-algebras. -/
  [tower : IsScalarTower A carrier S]
  /-- `S` is the localization of the descended algebra at the image of `M`. -/
  isLocalization : IsLocalization (Algebra.algebraMapSubmonoid carrier M) S

attribute [instance] LocalizationDescent.commRing LocalizationDescent.algebra
  LocalizationDescent.etale LocalizationDescent.algebraS LocalizationDescent.tower

/-- **Stacks 00U2 (10) (Algebra, Lemma 10.143.3).** An étale algebra over a localization `M⁻¹A` is
the base change of an étale algebra over `A`; equivalently, it is the localization of an étale
`A`-algebra at the image of `M`.

It is proved below as `StacksDraft.ArtinApproximation.etaleDescentAlongLocalization`. -/
def EtaleDescentAlongLocalization : Prop :=
  ∀ (A : Type u) [CommRing A] (M : Submonoid A) (L : Type u) [CommRing L] [Algebra A L]
    [IsLocalization M L] (S : Type u) [CommRing S] [Algebra L S] [Algebra A S]
    [IsScalarTower A L S], Algebra.Etale L S → Nonempty (LocalizationDescent A M L S)

/-- **Algebra, Lemma 00U2 (10).** An étale algebra over a localization `M⁻¹A` is the localization
of an étale `A`-algebra at the image of `M`.

This is `AlgebraicGeometry.exists_etale_pushout_of_localization`, which states the
conclusion as a pushout square of `CommRingCat`; the square is turned into the localization form
by `CommRingCat.isPushout_iff_isPushout` and `Algebra.isLocalization_iff_isPushout`. -/
theorem etaleDescentAlongLocalization : EtaleDescentAlongLocalization.{u} := by
  intro A _ M L _ _ _ S _ _ _ _ hetale
  obtain ⟨E, aa, bb, ha, hpo⟩ := AlgebraicGeometry.exists_etale_pushout_of_localization A L S M
    (algebraMap L S) (RingHom.etale_algebraMap.mpr hetale)
  let : Algebra A (E : Type u) := aa.hom.toAlgebra
  let : Algebra (E : Type u) S := bb.hom.toAlgebra
  have hetE : Algebra.Etale A (E : Type u) := RingHom.etale_algebraMap.mp ha
  have htow : IsScalarTower A (E : Type u) S := by
    refine IsScalarTower.of_algebraMap_eq fun r => ?_
    have h := congrArg (fun φ => CommRingCat.Hom.hom φ r) hpo.w
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
      CommRingCat.hom_ofHom] at h
    rw [IsScalarTower.algebraMap_apply A L S r]
    exact h
  have halg : Algebra.IsPushout A L (E : Type u) S :=
    CommRingCat.isPushout_iff_isPushout.mp hpo
  have hloc : IsLocalization (Algebra.algebraMapSubmonoid (E : Type u) M) S :=
    (Algebra.isLocalization_iff_isPushout (S := M) (A := L)).mpr halg.symm
  exact ⟨{ carrier := (E : Type u), isLocalization := hloc }⟩

/-! ### Auxiliary lemmas -/

/-- Residue field maps compose. -/
private theorem residueField_map_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) [I.IsPrime] (J : Ideal B) [J.IsPrime] (K : Ideal C) [K.IsPrime]
    (g : A →+* B) (h : B →+* C) (φ : A →+* C) (hφ : φ = h.comp g)
    (hIJ : I = J.comap g) (hJK : J = K.comap h) (hIK : I = K.comap φ) :
    Ideal.ResidueField.map I K φ hIK =
      (Ideal.ResidueField.map J K h hJK).comp (Ideal.ResidueField.map I J g hIJ) := by
  refine Ideal.ResidueField.ringHom_ext ?_
  ext r
  simp [hφ]

/-- Transporting an equality of residue classes back along a ring isomorphism. -/
private theorem quotient_mk_eq_of_ringEquiv {R T : Type u} [CommRing R] [CommRing T]
    (I : Ideal R) (e : R ≃+* T) {x y : R}
    (hxy : Ideal.Quotient.mk (I.map (e : R →+* T)) (e x)
      = Ideal.Quotient.mk (I.map (e : R →+* T)) (e y)) :
    Ideal.Quotient.mk I x = Ideal.Quotient.mk I y := by
  rw [Ideal.Quotient.eq] at hxy ⊢
  rw [← map_sub, Ideal.map_comap_of_equiv, Ideal.mem_comap] at hxy
  simpa using hxy

/-- How `completionComparison` acts on the quotient by the `N`-th power of the maximal ideal. -/
private theorem evalₐ_completionComparison_mk {A B : Type u} [CommRing A] [CommRing B]
    (p : Ideal A) [p.IsPrime] (q : Ideal B) [q.IsPrime] (g : A →+* B) (hpq : p = q.comap g)
    (N : ℕ) (x : Completion p) (y : Localization.AtPrime p)
    (hy : AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime p)) N x
      = Ideal.Quotient.mk _ y) :
    AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q)) N
        (completionComparison p q g hpq x)
      = Ideal.Quotient.mk _ (Localization.localRingHom p q g hpq y) := by
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q) :=
    (Localization.localRingHom p q g hpq).toAlgebra
  rw [completionComparison, Stacks.Nagata.PthRootDescent.evalₐ_mapAdicCompletion, hy,
    Ideal.quotientMap_mk]
  rfl

/-! ### Descending a solution to a principal localization -/

/-- The outcome of descending a solution from a localization of an étale algebra to a principal
localization of that algebra: a still étale `A`-algebra, of which `S` is again a localization,
carrying a solution of the system which induces the given one. -/
private structure AwaySolution (A : Type u) [CommRing A] (S : Type u) [CommRing S]
    [Algebra A S] {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) A) (sol : Fin n → S) where
  /-- The étale `A`-algebra carrying the descended solution. -/
  carrier : Type u
  /-- Its ring structure. -/
  [commRing : CommRing carrier]
  /-- Its algebra structure over `A`. -/
  [algebra : Algebra A carrier]
  /-- It is étale over `A`. -/
  [etale : Algebra.Etale A carrier]
  /-- Its map to `S`. -/
  [algebraS : Algebra carrier S]
  /-- That map is one of `A`-algebras. -/
  [tower : IsScalarTower A carrier S]
  /-- A submonoid exhibiting `S` as a localization of the carrier. -/
  loc : Submonoid carrier
  /-- `S` is that localization. -/
  isLocalization : IsLocalization loc S
  /-- The descended solution. -/
  b : Fin n → carrier
  /-- It solves the system. -/
  eval_b : ∀ j, MvPolynomial.eval₂ (algebraMap A carrier) b (f j) = 0
  /-- It induces the given solution in `S`. -/
  map_b : ∀ i, algebraMap carrier S (b i) = sol i

attribute [instance] AwaySolution.commRing AwaySolution.algebra AwaySolution.etale
  AwaySolution.algebraS AwaySolution.tower

/-- Inverting an element of `R` that is already a unit in `S` factors the `R`-algebra `S` through
its principal localization, compatibly with every algebra over which `S` is a tower. -/
private theorem exists_away_algebra {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S] (w : R)
    (hw : IsUnit (algebraMap R S w)) :
    ∃ _ : Algebra (Localization.Away w) S, IsScalarTower R (Localization.Away w) S ∧
      IsScalarTower A (Localization.Away w) S := by
  let : Algebra (Localization.Away w) S := (IsLocalization.Away.lift w hw).toAlgebra
  have htow : IsScalarTower R (Localization.Away w) S :=
    IsScalarTower.of_algebraMap_eq fun z => (IsLocalization.Away.lift_eq w hw z).symm
  refine ⟨this, htow, IsScalarTower.of_algebraMap_eq fun r => ?_⟩
  rw [IsScalarTower.algebraMap_apply A R (Localization.Away w) r,
    ← IsScalarTower.algebraMap_apply R (Localization.Away w) S,
    ← IsScalarTower.algebraMap_apply A R S]

/-- A ring map in a scalar tower carries the value of a polynomial at `b` to its value at the
image of `b`. -/
private theorem algebraMap_eval₂ {A R S : Type u} [CommRing A] [CommRing R] [CommRing S]
    [Algebra A R] [Algebra R S] [Algebra A S] [IsScalarTower A R S] {n : ℕ} (b : Fin n → R)
    (p : MvPolynomial (Fin n) A) :
    algebraMap R S (MvPolynomial.eval₂ (algebraMap A R) b p)
      = MvPolynomial.eval₂ (algebraMap A S) (fun i => algebraMap R S (b i)) p := by
  simpa [MvPolynomial.aeval_def, Function.comp_def] using
    (MvPolynomial.aeval_algebraMap_apply S b p).symm

/-- The source's step "after replacing `R'` by a principal localization if necessary we may
assume the `b'_i` come from `R'`": a solution in a localization `S` of an étale `A`-algebra `E`
at the image of `M` comes from a principal localization of `E` at the image of an element of `M`,
which is again étale over `A` and of which `S` is again a localization. -/
private theorem exists_awaySolution {A S : Type u} [CommRing A] [CommRing S] [Algebra A S]
    (M : Submonoid A) (E : Type u) [CommRing E] [Algebra A E] [Algebra.Etale A E] [Algebra E S]
    [IsScalarTower A E S] [IsLocalization (Algebra.algebraMapSubmonoid E M) S]
    {n m : ℕ} (f : Fin m → MvPolynomial (Fin n) A) (sol : Fin n → S)
    (hsol : ∀ j, MvPolynomial.eval₂ (algebraMap A S) sol (f j) = 0) :
    Nonempty (AwaySolution A S f sol) := by
  classical
  -- Write each coordinate of the solution as a fraction over `E`.
  have hfrac : ∀ i, ∃ (x : E) (c : M),
      sol i * algebraMap E S (algebraMap A E (c : A)) = algebraMap E S x := by
    intro i
    obtain ⟨⟨x, s⟩, e⟩ := IsLocalization.surj (Algebra.algebraMapSubmonoid E M) (sol i)
    obtain ⟨c, hc, hcs⟩ := Submonoid.mem_map.mp s.2
    exact ⟨x, ⟨c, hc⟩, by rw [show algebraMap A E c = (s : E) from hcs]; exact e⟩
  choose x c hxc using hfrac
  -- A common denominator for the `n` coordinates.
  set u : A := ∏ i, (c i : A) with hu
  have hu_mem : u ∈ M := Submonoid.prod_mem _ fun i _ => (c i).2
  set w : E := algebraMap A E u with hw
  have hw_mem : w ∈ Algebra.algebraMapSubmonoid E M := ⟨u, hu_mem, rfl⟩
  set d : Fin n → A := fun i => ∏ k ∈ Finset.univ.erase i, (c k : A) with hd
  have hud : ∀ i, u = (c i : A) * d i := fun i =>
    (Finset.mul_prod_erase Finset.univ (fun k => (c k : A)) (Finset.mem_univ i)).symm
  have hsolw : ∀ i, sol i * algebraMap E S w = algebraMap E S (x i * algebraMap A E (d i)) := by
    intro i
    rw [hw, hud i, map_mul, map_mul, ← mul_assoc, hxc i, ← map_mul]
  have hwunit : IsUnit (algebraMap E S w) :=
    IsLocalization.map_units S (⟨w, hw_mem⟩ : Algebra.algebraMapSubmonoid E M)
  -- Stage one: the coordinates are defined over `E[1/w]`.
  obtain ⟨_, htow1, htowA1⟩ := exists_away_algebra (A := A) w hwunit
  have hloc1 : IsLocalization ((Algebra.algebraMapSubmonoid E M).map
      (algebraMap E (Localization.Away w))) S :=
    IsLocalization.isLocalization_of_submonoid_le (Localization.Away w) S (Submonoid.powers w)
      (Algebra.algebraMapSubmonoid E M) (Submonoid.powers_le.mpr hw_mem)
  set b : Fin n → Localization.Away w := fun i =>
    IsLocalization.mk' (Localization.Away w) (x i * algebraMap A E (d i))
      (⟨w, Submonoid.mem_powers w⟩ : Submonoid.powers w) with hb
  have hbS : ∀ i, algebraMap (Localization.Away w) S (b i) = sol i := by
    intro i
    have h1 : b i * algebraMap E (Localization.Away w) w
        = algebraMap E (Localization.Away w) (x i * algebraMap A E (d i)) :=
      IsLocalization.mk'_spec _ _ _
    have h2 := congrArg (algebraMap (Localization.Away w) S) h1
    rw [map_mul] at h2
    simp only [← IsScalarTower.algebraMap_apply] at h2
    exact hwunit.mul_right_cancel (h2.trans (hsolw i).symm)
  -- Stage two: the equations hold after inverting one more element of `M`.
  set y : Fin m → Localization.Away w := fun j =>
    MvPolynomial.eval₂ (algebraMap A (Localization.Away w)) b (f j) with hy
  have hyS : ∀ j, algebraMap (Localization.Away w) S (y j) = 0 := by
    intro j
    simp only [hy, algebraMap_eval₂, hbS]
    exact hsol j
  have hvex : ∀ j, ∃ v : M, algebraMap A (Localization.Away w) (v : A) * y j = 0 := by
    intro j
    obtain ⟨z, hz⟩ := IsLocalization.exists_of_eq
      (M := (Algebra.algebraMapSubmonoid E M).map (algebraMap E (Localization.Away w)))
      (S := S) (x := y j) (y := 0) (by rw [hyS j, _root_.map_zero])
    obtain ⟨z', hz', hz'z⟩ := Submonoid.mem_map.mp z.2
    obtain ⟨v, hv, hvz⟩ := Submonoid.mem_map.mp hz'
    refine ⟨⟨v, hv⟩, ?_⟩
    have heq : algebraMap A (Localization.Away w) v = (z : Localization.Away w) := by
      rw [IsScalarTower.algebraMap_apply A E (Localization.Away w), hvz, hz'z]
    rw [heq, hz, mul_zero]
  choose v hv using hvex
  set v₀ : A := ∏ j, (v j : A) with hv₀
  have hv₀_mem : v₀ ∈ M := Submonoid.prod_mem _ fun j _ => (v j).2
  set w₂ : Localization.Away w := algebraMap A (Localization.Away w) v₀ with hw₂
  have hw₂unit : IsUnit (algebraMap (Localization.Away w) S w₂) := by
    rw [hw₂, ← IsScalarTower.algebraMap_apply A (Localization.Away w) S,
      IsScalarTower.algebraMap_apply A E S]
    exact IsLocalization.map_units S (⟨algebraMap A E v₀, v₀, hv₀_mem, rfl⟩ :
      Algebra.algebraMapSubmonoid E M)
  obtain ⟨_, htow2, htowA2⟩ := exists_away_algebra (A := A) w₂ hw₂unit
  have hyzero : ∀ j, algebraMap (Localization.Away w) (Localization.Away w₂) (y j) = 0 := by
    intro j
    have h0 : IsUnit (algebraMap (Localization.Away w) (Localization.Away w₂) w₂) :=
      IsLocalization.map_units (Localization.Away w₂)
        (⟨w₂, Submonoid.mem_powers w₂⟩ : Submonoid.powers w₂)
    refine (h0.mul_right_eq_zero).mp ?_
    have hvj : v₀ = (v j : A) * ∏ k ∈ Finset.univ.erase j, (v k : A) :=
      (Finset.mul_prod_erase Finset.univ (fun k => (v k : A)) (Finset.mem_univ j)).symm
    have : algebraMap (Localization.Away w) (Localization.Away w₂) (w₂ * y j) = 0 := by
      rw [hw₂, hvj, map_mul, mul_comm (algebraMap A (Localization.Away w) (v j : A)),
        mul_assoc, hv j, mul_zero, _root_.map_zero]
    rwa [map_mul] at this
  -- Assemble.
  refine ⟨{
    carrier := Localization.Away w₂
    loc := ((Algebra.algebraMapSubmonoid E M).map (algebraMap E (Localization.Away w))).map
      (algebraMap (Localization.Away w) (Localization.Away w₂))
    isLocalization := IsLocalization.isLocalization_of_submonoid_le (Localization.Away w₂) S
      (Submonoid.powers w₂)
      ((Algebra.algebraMapSubmonoid E M).map (algebraMap E (Localization.Away w)))
      (Submonoid.powers_le.mpr ⟨algebraMap A E v₀, ⟨v₀, hv₀_mem, rfl⟩, by
        rw [hw₂, IsScalarTower.algebraMap_apply A E (Localization.Away w)]⟩)
    b := fun i => algebraMap (Localization.Away w) (Localization.Away w₂) (b i)
    eval_b := fun j => by
      rw [← algebraMap_eval₂]
      exact hyzero j
    map_b := fun i => by
      rw [← IsScalarTower.algebraMap_apply (Localization.Away w) (Localization.Away w₂) S]
      exact hbS i }⟩

/-- The transport of the congruence along the identification of `A'_{𝔭'}` with `S_q`: both are
the localization of `A'` at `𝔭'`, so a congruence modulo the `N`-th power of the maximal ideal
read in the one is the same congruence read in the other. -/
private theorem approx_transport {A W S : Type u} [CommRing A] [CommRing W] [CommRing S]
    [Algebra A W] [Algebra W S] [Algebra A S] [IsScalarTower A W S]
    (p : Ideal A) [p.IsPrime] [Algebra (Localization.AtPrime p) S]
    [IsScalarTower A (Localization.AtPrime p) S] (q : Ideal S) [q.IsPrime]
    (hq : maximalIdeal (Localization.AtPrime p)
      = q.comap (algebraMap (Localization.AtPrime p) S))
    (hcp : p = (q.comap (algebraMap W S)).comap (algebraMap A W))
    [(q.comap (algebraMap W S)).IsPrime]
    [IsLocalization.AtPrime (Localization.AtPrime q) (q.comap (algebraMap W S))]
    [IsNoetherianRing (Localization.AtPrime (q.comap (algebraMap W S)))]
    (N : ℕ) (aa : Completion p) (bb : W) (ss : S) (hbs : algebraMap W S bb = ss)
    (happrox : localCompletionComparison q hq aa - toCompletion q ss ∈ completionIdeal q N) :
    completionComparison p (q.comap (algebraMap W S)) (algebraMap A W) hcp aa
      - toCompletion (q.comap (algebraMap W S)) bb
      ∈ completionIdeal (q.comap (algebraMap W S)) N := by
  classical
  set e : Localization.AtPrime (q.comap (algebraMap W S)) ≃+* Localization.AtPrime q :=
    (IsLocalization.algEquiv (q.comap (algebraMap W S)).primeCompl
      (Localization.AtPrime (q.comap (algebraMap W S))) (Localization.AtPrime q)).toRingEquiv
    with he
  have hcomm : ∀ x : W,
      e (algebraMap W (Localization.AtPrime (q.comap (algebraMap W S))) x)
      = algebraMap W (Localization.AtPrime q) x := fun x => by
    rw [he]; exact AlgEquiv.commutes _ x
  have hmaxL : Ideal.map (algebraMap W (Localization.AtPrime (q.comap (algebraMap W S))))
      (q.comap (algebraMap W S))
      = maximalIdeal (Localization.AtPrime (q.comap (algebraMap W S))) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal _ _
  have hmaxSq : Ideal.map (algebraMap W (Localization.AtPrime q)) (q.comap (algebraMap W S))
      = maximalIdeal (Localization.AtPrime q) :=
    IsLocalization.AtPrime.map_eq_maximalIdeal _ _
  have hecomp : (e : Localization.AtPrime (q.comap (algebraMap W S)) →+*
      Localization.AtPrime q).comp
      (algebraMap W (Localization.AtPrime (q.comap (algebraMap W S))))
      = algebraMap W (Localization.AtPrime q) := RingHom.ext hcomm
  have hmaxe : Ideal.map (e : Localization.AtPrime (q.comap (algebraMap W S)) →+*
      Localization.AtPrime q)
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap W S))))
      = maximalIdeal (Localization.AtPrime q) := by
    rw [← hmaxL, Ideal.map_map, hecomp, hmaxSq]
  -- The two maps out of `A_𝔭` into `S_q` agree, both being determined on `A`.
  have hmapsagree : (e : Localization.AtPrime (q.comap (algebraMap W S)) →+*
      Localization.AtPrime q).comp
      (Localization.localRingHom p (q.comap (algebraMap W S)) (algebraMap A W) hcp)
      = (algebraMap S (Localization.AtPrime q)).comp
        (algebraMap (Localization.AtPrime p) S) := by
    refine IsLocalization.ringHom_ext p.primeCompl ?_
    ext r
    simp only [RingHom.coe_comp, Function.comp_apply, Localization.localRingHom_to_map]
    rw [show (e : Localization.AtPrime (q.comap (algebraMap W S)) →+* Localization.AtPrime q)
        (algebraMap W _ (algebraMap A W r))
        = algebraMap W (Localization.AtPrime q) (algebraMap A W r) from hcomm _,
      show algebraMap W (Localization.AtPrime q) (algebraMap A W r)
        = algebraMap S (Localization.AtPrime q) (algebraMap W S (algebraMap A W r)) from
        IsScalarTower.algebraMap_apply W S (Localization.AtPrime q) _,
      ← IsScalarTower.algebraMap_apply A W S,
      IsScalarTower.algebraMap_apply A (Localization.AtPrime p) S]
  refine mem_completionIdeal_of_evalₐ_eq_zero _ ?_
  obtain ⟨z, hz⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime p)) N aa)
  -- The hypothesis, read in `S_q ⧸ 𝔪_q^N`.
  have hyp := evalₐ_eq_zero_of_mem_completionIdeal q happrox
  rw [map_sub, evalₐ_localCompletionComparison_mk q hq N aa z hz.symm,
    show AdicCompletion.evalₐ (maximalIdeal (Localization.AtPrime q)) N (toCompletion q ss)
      = Ideal.Quotient.mk _ (algebraMap S (Localization.AtPrime q) ss) from
      AdicCompletion.evalₐ_of (maximalIdeal (Localization.AtPrime q)) N _,
    sub_eq_zero] at hyp
  -- The goal, read in `A'_{𝔭'} ⧸ 𝔪_{𝔭'}^N` and transported along `e`.
  rw [map_sub, evalₐ_completionComparison_mk p _ (algebraMap A W) hcp N aa z hz.symm,
    show AdicCompletion.evalₐ
        (maximalIdeal (Localization.AtPrime (q.comap (algebraMap W S)))) N
        (toCompletion (q.comap (algebraMap W S)) bb)
      = Ideal.Quotient.mk _
        (algebraMap W (Localization.AtPrime (q.comap (algebraMap W S))) bb) from
      AdicCompletion.evalₐ_of
        (maximalIdeal (Localization.AtPrime (q.comap (algebraMap W S)))) N _,
    sub_eq_zero]
  refine quotient_mk_eq_of_ringEquiv _ (e : Localization.AtPrime (q.comap (algebraMap W S))
    ≃+* Localization.AtPrime q) ?_
  rw [show Ideal.map (e : Localization.AtPrime (q.comap (algebraMap W S)) →+*
      Localization.AtPrime q)
      (maximalIdeal (Localization.AtPrime (q.comap (algebraMap W S))) ^ N)
      = maximalIdeal (Localization.AtPrime q) ^ N from by rw [Ideal.map_pow, hmaxe],
    show e (Localization.localRingHom p (q.comap (algebraMap W S)) (algebraMap A W) hcp z)
      = algebraMap S (Localization.AtPrime q) (algebraMap (Localization.AtPrime p) S z) from
      RingHom.congr_fun hmapsagree z,
    show e (algebraMap W (Localization.AtPrime (q.comap (algebraMap W S))) bb)
      = algebraMap S (Localization.AtPrime q) ss from by
      rw [hcomm bb, IsScalarTower.algebraMap_apply W S (Localization.AtPrime q) bb, hbs]]
  exact hyp


/-! ### Stacks 0CAR -/

/-- **Stacks 0CAR (Smoothing Ring Maps, Lemma 16.13.4).** Let `A` be a Noetherian ring, let `𝔭`
be a prime of `A` such that `A_𝔭` is a G-ring, and let `f₁, …, f_m` be polynomials over `A` in
`n` variables. If the system `f = 0` has a solution `(a₁, …, a_n)` in the completion of `A_𝔭`,
then for every `N` there are an étale ring map `A → A'`, a prime `𝔭' ⊂ A'` lying over `𝔭` with
`κ(𝔭) = κ(𝔭')`, and a solution `(b₁, …, b_n)` of the system in `A'` with
`a_i - b_i ∈ (𝔭')^N (A'_{𝔭'})^∧`.

The hypothesis `h07QZ` is the first input of the source's proof, Theorem 07QZ, the same
statement for a Noetherian local G-ring, which the source deduces from Popescu's theorem (07GC).
The second input, Algebra, Lemma 00U2 (10), the finite-stage descent of an étale algebra along a
localization, is `StacksDraft.ArtinApproximation.etaleDescentAlongLocalization`. Everything else
is proved here.

This is the reduction rather than the lemma: `h07QZ` is
`StacksDraft.ArtinApproximation.localApproximationProperty`, and the lemma itself, with no
hypotheses, is `StacksDraft.ArtinApproximation.artinApproximationGRing`. -/
theorem artinApproximationGRing_of_local (h07QZ : LocalApproximationProperty.{u}) :
    ArtinApproximationGRing.{u} := by
  classical
  intro A _ p _ hAnoeth hG n m f N a hf
  have hLnoeth : IsNoetherianRing (Localization.AtPrime p) :=
    IsLocalization.isNoetherianRing p.primeCompl (Localization.AtPrime p) hAnoeth
  have hpm : p = (maximalIdeal (Localization.AtPrime p)).comap
      (algebraMap A (Localization.AtPrime p)) :=
    (Localization.AtPrime.under_maximalIdeal (I := p)).symm
  -- The system base changed to `A_𝔭`, of which `a` is still a solution in the completion.
  have hsolL : ∀ j, MvPolynomial.eval₂
      (algebraMap (Localization.AtPrime p) (Completion p)) a
      (MvPolynomial.map (algebraMap A (Localization.AtPrime p)) (f j)) = 0 := fun j => by
    rw [MvPolynomial.eval₂_map]
    exact hf j
  obtain ⟨sd⟩ := h07QZ (Localization.AtPrime p) hLnoeth hG n m
    (fun j => MvPolynomial.map (algebraMap A (Localization.AtPrime p)) (f j)) N a hsolL
  -- The étale `A_𝔭`-algebra `S` is an `A`-algebra through `A_𝔭`.
  let : Algebra A sd.carrier :=
    ((algebraMap (Localization.AtPrime p) sd.carrier).comp
      (algebraMap A (Localization.AtPrime p))).toAlgebra
  have htowALS : IsScalarTower A (Localization.AtPrime p) sd.carrier :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  -- Descend `S` to an étale `A`-algebra, of which it is a localization.
  obtain ⟨dd⟩ := etaleDescentAlongLocalization A p.primeCompl (Localization.AtPrime p)
    sd.carrier sd.etale
  have := dd.isLocalization
  -- Descend the solution and its equations to a principal localization.
  have hsolA : ∀ j, MvPolynomial.eval₂ (algebraMap A sd.carrier) sd.sol (f j) = 0 := by
    intro j
    rw [IsScalarTower.algebraMap_eq A (Localization.AtPrime p) sd.carrier,
      ← MvPolynomial.eval₂_map]
    exact sd.eval_sol j
  obtain ⟨ws⟩ := exists_awaySolution p.primeCompl dd.carrier f sd.sol hsolA
  have := ws.isLocalization
  have hAprime : (sd.prime.comap (algebraMap ws.carrier sd.carrier)).IsPrime := inferInstance
  have hnoethW : IsNoetherianRing ws.carrier := Algebra.FiniteType.isNoetherianRing A ws.carrier
  have hnoethP : IsNoetherianRing
      (Localization.AtPrime (sd.prime.comap (algebraMap ws.carrier sd.carrier))) :=
    IsLocalization.isNoetherianRing
      (sd.prime.comap (algebraMap ws.carrier sd.carrier)).primeCompl _ hnoethW
  -- `𝔭'` lies over `𝔭`.
  have hAq : p = sd.prime.comap (algebraMap A sd.carrier) := by
    rw [IsScalarTower.algebraMap_eq A (Localization.AtPrime p) sd.carrier, ← Ideal.comap_comap,
      ← sd.comap_prime]
    exact hpm
  have hcp : p = (sd.prime.comap (algebraMap ws.carrier sd.carrier)).comap
      (algebraMap A ws.carrier) := by
    rw [Ideal.comap_comap, ← IsScalarTower.algebraMap_eq A ws.carrier sd.carrier]
    exact hAq
  -- The residue field equality `κ(𝔭) = κ(𝔭')`.
  have hres1 : Function.Bijective (Ideal.ResidueField.map p
      (maximalIdeal (Localization.AtPrime p)) (algebraMap A (Localization.AtPrime p))
      hpm) :=
    (RingHom.surjectiveOnStalks_of_isLocalization p.primeCompl
      (Localization.AtPrime p)).residueFieldMap_bijective _ _ _
  have hres3 : Function.Bijective (Ideal.ResidueField.map
      (sd.prime.comap (algebraMap ws.carrier sd.carrier)) sd.prime
      (algebraMap ws.carrier sd.carrier) rfl) :=
    (RingHom.surjectiveOnStalks_of_isLocalization ws.loc
      sd.carrier).residueFieldMap_bijective _ _ _
  have hcomp1 := residueField_map_comp p (maximalIdeal (Localization.AtPrime p)) sd.prime
    (algebraMap A (Localization.AtPrime p)) (algebraMap (Localization.AtPrime p) sd.carrier)
    (algebraMap A sd.carrier)
    (IsScalarTower.algebraMap_eq A (Localization.AtPrime p) sd.carrier)
    hpm sd.comap_prime hAq
  have hcomp2 := residueField_map_comp p
    (sd.prime.comap (algebraMap ws.carrier sd.carrier)) sd.prime (algebraMap A ws.carrier)
    (algebraMap ws.carrier sd.carrier) (algebraMap A sd.carrier)
    (IsScalarTower.algebraMap_eq A ws.carrier sd.carrier) hcp rfl hAq
  have hbijAq : Function.Bijective
      (Ideal.ResidueField.map p sd.prime (algebraMap A sd.carrier) hAq) := by
    rw [hcomp1]
    simpa only [RingHom.coe_comp] using sd.residueField_bijective.comp hres1
  have hfinal : Function.Bijective (Ideal.ResidueField.map p
      (sd.prime.comap (algebraMap ws.carrier sd.carrier)) (algebraMap A ws.carrier) hcp) := by
    rw [hcomp2] at hbijAq
    simp only [RingHom.coe_comp] at hbijAq
    exact (Function.Bijective.of_comp_iff' hres3 _).mp hbijAq
  -- `S_q` is also the localization of the descended algebra at `𝔭'`.
  have hAtP : IsLocalization.AtPrime (Localization.AtPrime sd.prime)
      (sd.prime.comap (algebraMap ws.carrier sd.carrier)) :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization ws.loc
      (Localization.AtPrime sd.prime) sd.prime
  -- Assemble the étale solution over `A`.
  exact ⟨{ carrier := ws.carrier
           prime := sd.prime.comap (algebraMap ws.carrier sd.carrier)
           comap_prime := hcp
           residueField_bijective := hfinal
           sol := ws.b
           eval_sol := ws.eval_b
           approx := fun i => approx_transport p sd.prime sd.comap_prime hcp N (a i)
             (ws.b i) (sd.sol i) (ws.map_b i) (sd.approx i) }⟩

/-! ### Theorem 07QZ in that shape, and Stacks 0CAR -/

/-- **Theorem 07QZ in the shape Lemma 0CAR consumes it.** For a Noetherian local G-ring, a
polynomial system with a solution in the completion has, for every `N`, an étale solution in the
sense of `StacksDraft.ArtinApproximation.LocalEtaleSolution`.

This is `Stacks.Smoothing.exists_localEtaleSolution_of_isGRing`, forgetting the three
conclusions that the structure does not record: maximality of the distinguished prime, the map
into `R^∧`, and the congruence read there. -/
theorem localApproximationProperty : LocalApproximationProperty.{u} := by
  intro L _ _ hnoeth hG n m f N a hf
  let : IsNoetherianRing L := hnoeth
  obtain ⟨s, -⟩ := Stacks.Smoothing.exists_localEtaleSolution_of_isGRing hG f N a
    fun j => by rw [MvPolynomial.aeval_def]; exact hf j
  exact ⟨s⟩

/-- **Stacks 0CAR (Smoothing Ring Maps, Lemma 16.13.4).** Let `A` be a Noetherian ring, let `𝔭`
be a prime of `A` such that `A_𝔭` is a G-ring, and let `f₁, …, f_m` be polynomials over `A` in
`n` variables. If the system `f = 0` has a solution `(a₁, …, a_n)` in the completion of `A_𝔭`,
then for every `N` there are an étale ring map `A → A'`, a prime `𝔭' ⊂ A'` lying over `𝔭` with
`κ(𝔭) = κ(𝔭')`, and a solution `(b₁, …, b_n)` of the system in `A'` with
`a_i - b_i ∈ (𝔭')^N (A'_{𝔭'})^∧`.

Both inputs of the source's proof are proved: Theorem 07QZ is `localApproximationProperty` and
Algebra, Lemma 00U2 (10) is `etaleDescentAlongLocalization`. -/
@[stacks 0CAR "the full conclusion — étaleness of `A → A'`, `𝔭'` lying over `𝔭`, the solution \
in `A'`, the residue field equality `κ(𝔭) = κ(𝔭')` and the congruence \
`a_i - b_i ∈ (𝔭')^N (A'_{𝔭'})^∧` for every `i` and every `N` — in the spelling of \
`StacksDraft.ArtinApproximation.ArtinApproximationGRing`, with NO carried hypotheses. The \
source's proof has two inputs and both are proved. The second, Algebra Lemma 00U2 (10), is \
`etaleDescentAlongLocalization`, from the public \
`AlgebraicGeometry.exists_etale_pushout_of_localization`. The first is Theorem 07QZ, \
`Stacks.Smoothing.exists_localEtaleSolution_of_isGRing`, itself unconditional because \
Popescu's Theorem 07GC is (`indSmooth_of_isRegularRingMap`, resting on Lemma 07FJ \
`canBeResolvedInPositiveCharacteristic`, whose λ-choice repair is due to Brian Nugent); the \
shape 0CAR's proof consumes it in is `localApproximationProperty`. The reduction of 0CAR to \
07QZ — the base change of the system to `A_𝔭`, the descent of the solution and its equations to \
a principal localization, the identification of `𝔭'` and of `A'_{𝔭'}` with `S_q`, the residue \
field equality and the transport of the congruence — is `artinApproximationGRing_of_local`."]
theorem artinApproximationGRing : ArtinApproximationGRing.{u} :=
  artinApproximationGRing_of_local localApproximationProperty

end StacksDraft.ArtinApproximation
