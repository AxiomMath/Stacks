module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.PthRootFormsDecomposition
public import StacksFrontier.RingTheory.AdicCompletion.AdditiveFunctoriality

/-!
# Tag 07N1 over the `p`-adic completions

`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/PthRootFormsDecomposition.lean` proves
the conclusion of [Stacks, Lemma 60.25.3, Tag 07N1] for the **uncompleted** extension

`B ⟶ B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))`:

for a pair `(M, ∇)` over `B` with `∇` integrable, the canonical map of de Rham complexes
`c_M^• : M ⊗_B Ω^•_{B/A,γ} ⟶ M' ⊗_{B'} Ω^•_{B'/A,γ'}` admits a map `e_M^•` back such that both
composites are homotopic to multiplication by `p`.  The source takes `p`-adic completions
throughout.  This file proves two completed statements about the uncompleted extension: the
splitting of `D ⟶ D'` and the completion of the homotopy inverse.

## `D ⟶ D'` is a split injection of `D`-modules

The step of the source's proof which reads "`D'` is the `p`-adic completion of the free
`D`-module `⨁_{i < p} ⨁_{n ≥ 0} z^i ξ^[n] D`, so `D → D'` has a continuous `D`-linear section,
in particular `D → D'` is universally injective, i.e. (5) holds".  The uncompleted retraction is
`Crystalline.PthRootExtension.primeRetraction_comp` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/PurelyInseparablePullback.lean`, the
coordinate of the basis vector `z^0 ξ^[0] = 1`; completion is functorial for linear maps, so it
completes to `Crystalline.PthRootExtension.completedPrimeRetraction_comp_completedToPrimeRing`
and hence `Crystalline.PthRootExtension.injective_completedToPrimeRing`.  Here `D'` is the
`p`-adic completion of `B'`, which is exactly the source's `D'`.  The one difference from the
source is that `D` is the `p`-adic completion of `B` rather than `B` itself; the source's `D` is
already `p`-adically complete, which is neither used nor needed.

## The homotopy inverse over the completions

The homotopy inverse, both homotopies and the commutation with the differentials all survive the
`p`-adic completion of every term, because

* the completion of an additive map exists along `(p)` — the levels are cut out by the *integer*
  `pⁿ`, which is `Crystalline.PAdicCompletion.mapAddHom` — and
* that construction is a functor which is additive in the map, so a composite, a sum, a
  difference and an `ℕ`-multiple of additive maps all complete to the same combination of the
  completed maps.

The identities of [Stacks, Tag 07N1] are exactly combinations of those four shapes, so each one
is the image of its uncompleted counterpart under one functor.  The three transport lemmas
`Crystalline.PAdicCompletion.mapAddHom_comp_eq_comp`,
`Crystalline.PAdicCompletion.mapAddHom_comp_eq_nsmul_sub` and
`Crystalline.PAdicCompletion.mapAddHom_add_comp_eq_nsmul_sub` are those three shapes, and
`Crystalline.exists_completedHomotopyInverse_pthRootExtension_dividedPowerDifferentials` is their
instantiation.

Each term of either complex is completed along `(p)` read in the ring the term is a module over:
`(p) ⊆ B` for `M ⊗_B Ω^q_{B/A,γ}` and `(p) ⊆ B'` for `M' ⊗_{B'} Ω^q_{B'/A,γ'}`.  That the answer
does not depend on the ring the ideal is read in — the level is the subgroup `pⁿ ·` in either
case — is `Crystalline.PAdicCompletion.coe_pow_smul_top_eq`; it is what lets a single additive map
relate completions taken over the two different rings.

The de Rham differentials and the comparison `c_M^•` are `A`-linear maps between the
`RestrictScalars` synonyms, which is how `Crystalline.extendedConnection` produces them; here
they are read as additive maps of the underlying modules by
`Crystalline.restrictScalarsUnderlyingAddHom`, the composite with the identity additive
equivalences `RestrictScalars.addEquiv`, which changes nothing.

## Relation to the tag

The split injection is a step of the source's proof and not its conclusion.  The homotopy inverse
below is for the completions of the de Rham complexes of the uncompleted extension `B'`, whose
modules are uncompleted `B`-modules with ordinary connections.  [Stacks, Tag 07N1] itself — for a
module with a completed connection over `D` and the completed forms of the completed ring `D'` —
is `Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension` of
`StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/PthRootCompletedTheorem.lean`, which is
proved level by level and does not go through this file.

The maps `ê`, `ĥ` and `k̂` produced below are **additive**.
`Crystalline.exists_completedLinearHomotopyInverse_pthRootExtension_dividedPowerDifferentials`
of `StacksFrontier/AlgebraicGeometry/Crystalline/Differentials/PthRootCompletedLinear.lean` is the
same conclusion with the three maps linear over the completed base `D`.

## Main definitions

* `Crystalline.PthRootExtension.completedBaseRing`,
  `Crystalline.PthRootExtension.completedPrimeRing` — the rings `D` and `D'`.
* `Crystalline.PthRootExtension.completedToPrimeRing`,
  `Crystalline.PthRootExtension.completedPrimeRetraction` — `D ⟶ D'` and its retraction.
* `Crystalline.PthRootExtension.completedBaseDeRhamTerm`,
  `Crystalline.PthRootExtension.completedPrimeDeRhamTerm` — the terms of the two completed
  complexes.
* `Crystalline.PthRootExtension.completedBaseDeRhamDifferential`,
  `Crystalline.PthRootExtension.completedPrimeDeRhamDifferential` — their differentials, the
  completions of the extended connections.
* `Crystalline.PthRootExtension.completedComparisonMap` — `ĉ_M^•`.

## Main results

* `Crystalline.PAdicCompletion.mapAddHom_sub`,
  `Crystalline.PAdicCompletion.mapAddHom_nsmul` — the completion of an additive map is
  subtractive and `ℕ`-homogeneous in the map.
* `Crystalline.PAdicCompletion.coe_pow_smul_top_eq` — the levels of a `p`-adic filtration do not
  depend on the ring in which `(p)` is read.
* `Crystalline.PAdicCompletion.mapAddHom_comp_eq_comp`,
  `Crystalline.PAdicCompletion.mapAddHom_comp_eq_nsmul_sub`,
  `Crystalline.PAdicCompletion.mapAddHom_add_comp_eq_nsmul_sub` — the three shapes of identity
  that a homotopy equivalence up to `p` consists of, transported across the completion.
* `Crystalline.PthRootExtension.completedPrimeRetraction_comp_completedToPrimeRing` and
  `Crystalline.PthRootExtension.injective_completedToPrimeRing` — **`D ⟶ D'` is a split injection
  of `D`-modules.**
* `Crystalline.exists_completedHomotopyInverse_pthRootExtension_dividedPowerDifferentials` —
  **the conclusion of [Stacks, Tag 07N1] for the `p`-adic completions** of the de Rham complexes
  of the uncompleted extension.

## References

* [Stacks Project, Lemma 60.25.3, Tag 07N1](https://stacks.math.columbia.edu/tag/07N1)
* [Stacks Project, Lemma 60.6.9, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
* [Stacks Project, Lemma 60.25.2, Tag 07Q7](https://stacks.math.columbia.edu/tag/07Q7)
* [Stacks Project, Tag 07I0](https://stacks.math.columbia.edu/tag/07I0)
-/

@[expose] public noncomputable section

open DividedPowers Stacks.DeRham.DifferentialDescent

open scoped TensorProduct

universe u w

namespace Crystalline

namespace PAdicCompletion

/-! ### The completion of an additive map is subtractive and `ℕ`-homogeneous in the map -/

section MapAlgebra

variable (p : ℕ) (R : Type*) [CommRing R] (S : Type*) [CommRing S] {X : Type*} [AddCommGroup X]
  [Module R X] {Y : Type*} [AddCommGroup Y] [Module S Y]

/-- **The completion of a difference of additive maps is the difference of their completions.**
Immediate from `Crystalline.PAdicCompletion.mapAddHom_add`. -/
theorem mapAddHom_sub (f g : X →+ Y) :
    mapAddHom p R S (f - g) = mapAddHom p R S f - mapAddHom p R S g :=
  eq_sub_of_add_eq (by rw [← mapAddHom_add, sub_add_cancel])

/-- **The completion of an `ℕ`-multiple of an additive map is that multiple of its completion.**
By induction from `Crystalline.PAdicCompletion.mapAddHom_add`. -/
theorem mapAddHom_nsmul (n : ℕ) (f : X →+ Y) :
    mapAddHom p R S (n • f) = n • mapAddHom p R S f := by
  induction n with
  | zero => rw [zero_smul, zero_smul, mapAddHom_zero]
  | succ k ih => rw [succ_nsmul, succ_nsmul, mapAddHom_add, ih]

end MapAlgebra

/-! ### The levels do not depend on the ring in which `(p)` is read -/

section LevelIndependence

variable (p : ℕ) (R : Type*) [CommRing R] (S : Type*) [CommRing S] (X : Type*) [AddCommGroup X]
  [Module R X] [Module S X]

/-- **The level-`n` submodule of a `p`-adic filtration does not depend on the ring in which the
ideal `(p)` is read**: on either side it is the subgroup `pⁿ X`, by
`Crystalline.PAdicCompletion.mem_pow_smul_top_iff`.  This is the reason an additive map can
relate a completion taken over one base ring to a completion taken over another, which is what
`Crystalline.PAdicCompletion.mapAddHom` does and what the comparison of the two de Rham complexes
below needs. -/
theorem coe_pow_smul_top_eq (n : ℕ) :
    ((pAdicIdeal (A := R) p ^ n • ⊤ : Submodule R X) : Set X) =
      ((pAdicIdeal (A := S) p ^ n • ⊤ : Submodule S X) : Set X) := by
  ext z
  simp only [SetLike.mem_coe]
  rw [mem_pow_smul_top_iff p R n z, mem_pow_smul_top_iff p S n z]

end LevelIndependence

/-! ### The three shapes of identity, transported across the completion -/

section Transport

variable (p : ℕ) (R : Type*) [CommRing R] (S : Type*) [CommRing S] (T : Type*) [CommRing T]
  (U : Type*) [CommRing U] {X Y Z V : Type*} [AddCommGroup X] [Module R X] [AddCommGroup Y]
  [Module S Y] [AddCommGroup Z] [Module T Z] [AddCommGroup V] [Module U V]

/-- **A commuting square of additive maps stays commuting across the `p`-adic completion**, the
four modules living over four different base rings. -/
theorem mapAddHom_comp_eq_comp (f : X →+ Y) (g : Y →+ V) (f' : X →+ Z) (g' : Z →+ V)
    (hsq : g.comp f = g'.comp f') :
    (mapAddHom p S U g).comp (mapAddHom p R S f) =
      (mapAddHom p T U g').comp (mapAddHom p R T f') := by
  rw [← mapAddHom_comp p R S U f g, ← mapAddHom_comp p R T U f' g', hsq]

/-- **`g ∘ f = n - v ∘ u` stays true across the `p`-adic completion**, with `n` standing for
multiplication by the natural number `n`.  This is the shape of a homotopy identity in degree
zero. -/
theorem mapAddHom_comp_eq_nsmul_sub (n : ℕ) (f : X →+ Y) (g : Y →+ X) (u : X →+ Z) (v : Z →+ X)
    (hid : g.comp f = n • AddMonoidHom.id X - v.comp u) :
    (mapAddHom p S R g).comp (mapAddHom p R S f) =
      n • AddMonoidHom.id (AdicCompletion (pAdicIdeal (A := R) p) X) -
        (mapAddHom p T R v).comp (mapAddHom p R T u) := by
  rw [← mapAddHom_comp p R S R f g, hid, mapAddHom_sub, mapAddHom_nsmul, mapAddHom_id,
    mapAddHom_comp p R T R u v]

/-- **`g ∘ f + g' ∘ f' = n - v ∘ u` stays true across the `p`-adic completion**, with `n`
standing for multiplication by the natural number `n`.  This is the shape of a homotopy identity
in positive degree. -/
theorem mapAddHom_add_comp_eq_nsmul_sub (n : ℕ) (f : X →+ Y) (g : Y →+ X) (f' : X →+ V)
    (g' : V →+ X) (u : X →+ Z) (v : Z →+ X)
    (hid : g.comp f + g'.comp f' = n • AddMonoidHom.id X - v.comp u) :
    (mapAddHom p S R g).comp (mapAddHom p R S f) +
        (mapAddHom p U R g').comp (mapAddHom p R U f') =
      n • AddMonoidHom.id (AdicCompletion (pAdicIdeal (A := R) p) X) -
        (mapAddHom p T R v).comp (mapAddHom p R T u) := by
  rw [← mapAddHom_comp p R S R f g, ← mapAddHom_comp p R U R f' g', ← mapAddHom_add, hid,
    mapAddHom_sub, mapAddHom_nsmul, mapAddHom_id, mapAddHom_comp p R T R u v]

end Transport

end PAdicCompletion

/-! ### A map between `RestrictScalars` synonyms, read on the underlying modules -/

section RestrictScalarsReading

/-- An `A`-linear map between `RestrictScalars` synonyms, read as an additive map of the
underlying modules.  The two additive equivalences are `AddEquiv.refl`, so this changes nothing
about the map; it is what lets `Crystalline.PAdicCompletion.mapAddHom`, which completes over the
rings the modules are modules over, be applied to the `A`-linear differentials of
`Crystalline.extendedConnection`. -/
abbrev restrictScalarsUnderlyingAddHom {A S T X Y : Type*} [CommSemiring A] [Semiring S]
    [Semiring T] [Algebra A S] [Algebra A T] [AddCommMonoid X] [Module S X] [AddCommMonoid Y]
    [Module T Y] (f : RestrictScalars A S X →ₗ[A] RestrictScalars A T Y) : X →+ Y :=
  (RestrictScalars.addEquiv A T Y).toAddMonoidHom.comp
    (f.toAddMonoidHom.comp (RestrictScalars.addEquiv A S X).symm.toAddMonoidHom)

/-- Multiplication by the image of a natural number is the `ℕ`-multiple. -/
theorem restrictScalars_lsmul_natCast (R : Type*) (S : Type*) {X : Type*} [CommSemiring R]
    [Semiring S] [Algebra R S] [AddCommMonoid X] [Module S X] (n : ℕ)
    (x : RestrictScalars R S X) :
    RestrictScalars.lsmul R S X (n : S) x = n • x := by
  rw [RestrictScalars.lsmul_apply_apply, Nat.cast_smul_eq_nsmul, map_nsmul,
    AddEquiv.symm_apply_apply]

/-- Multiplication by the image of a natural number transported along an algebra map is the
`ℕ`-multiple. -/
theorem restrictScalars_lsmul_algebraMap_natCast (R : Type*) (S : Type*) (T : Type*) {X : Type*}
    [CommSemiring R] [CommSemiring S] [Semiring T] [Algebra R T] [Algebra S T] [AddCommMonoid X]
    [Module T X] (n : ℕ) (x : RestrictScalars R T X) :
    RestrictScalars.lsmul R T X (algebraMap S T (n : S)) x = n • x := by
  rw [map_natCast]
  exact restrictScalars_lsmul_natCast R T n x

end RestrictScalarsReading

/-! ### The two homotopy identities as identities of additive maps -/

section UnderlyingIdentities

variable {A S T : Type*} [CommRing A] [CommRing S] [CommRing T] [Algebra A S] [Algebra A T]
  {P Q Q' N : Type*} [AddCommGroup P] [Module T P] [AddCommGroup Q] [Module T Q]
  [AddCommGroup Q'] [Module T Q'] [AddCommGroup N] [Module S N]

/-- **A degree-zero homotopy identity, read as an identity of additive maps.**  The hypothesis is
the elementwise identity `g ∘ f = t - v ∘ u` with `t` acting as the `ℕ`-multiple by `n`; the
conclusion is the same identity between the underlying additive maps, which is the shape
`Crystalline.PAdicCompletion.mapAddHom_comp_eq_nsmul_sub` consumes. -/
theorem underlyingAddHom_comp_eq_nsmul_sub (n : ℕ) (t : T)
    (ht : ∀ x : RestrictScalars A T P, RestrictScalars.lsmul A T P t x = n • x)
    (f : RestrictScalars A T P →ₗ[A] RestrictScalars A T Q)
    (g : RestrictScalars A T Q →ₗ[A] RestrictScalars A T P)
    (u : RestrictScalars A T P →ₗ[A] RestrictScalars A S N)
    (v : RestrictScalars A S N →ₗ[A] RestrictScalars A T P)
    (hid : ∀ x : RestrictScalars A T P,
      g (f x) = RestrictScalars.lsmul A T P t x - v (u x)) :
    (restrictScalarsUnderlyingAddHom g).comp (restrictScalarsUnderlyingAddHom f) =
      n • AddMonoidHom.id P -
        (restrictScalarsUnderlyingAddHom v).comp (restrictScalarsUnderlyingAddHom u) :=
  AddMonoidHom.ext fun y ↦ (hid y).trans (by rw [ht y]; exact rfl)

/-- **A positive-degree homotopy identity, read as an identity of additive maps.**  The shape
`Crystalline.PAdicCompletion.mapAddHom_add_comp_eq_nsmul_sub` consumes. -/
theorem underlyingAddHom_add_comp_eq_nsmul_sub (n : ℕ) (t : T)
    (ht : ∀ x : RestrictScalars A T P, RestrictScalars.lsmul A T P t x = n • x)
    (f : RestrictScalars A T P →ₗ[A] RestrictScalars A T Q)
    (g : RestrictScalars A T Q →ₗ[A] RestrictScalars A T P)
    (f' : RestrictScalars A T P →ₗ[A] RestrictScalars A T Q')
    (g' : RestrictScalars A T Q' →ₗ[A] RestrictScalars A T P)
    (u : RestrictScalars A T P →ₗ[A] RestrictScalars A S N)
    (v : RestrictScalars A S N →ₗ[A] RestrictScalars A T P)
    (hid : ∀ x : RestrictScalars A T P,
      g (f x) + g' (f' x) = RestrictScalars.lsmul A T P t x - v (u x)) :
    (restrictScalarsUnderlyingAddHom g).comp (restrictScalarsUnderlyingAddHom f) +
        (restrictScalarsUnderlyingAddHom g').comp (restrictScalarsUnderlyingAddHom f') =
      n • AddMonoidHom.id P -
        (restrictScalarsUnderlyingAddHom v).comp (restrictScalarsUnderlyingAddHom u) :=
  AddMonoidHom.ext fun y ↦ (hid y).trans (by rw [ht y]; exact rfl)

/-- A degree-zero homotopy identity of `A`-linear maps, completed `p`-adically. -/
private theorem mapAddHom_underlying_comp_eq_nsmul_sub (p : ℕ) (t : T)
    (ht : ∀ x : RestrictScalars A T P, RestrictScalars.lsmul A T P t x = p • x)
    (f : RestrictScalars A T P →ₗ[A] RestrictScalars A T Q)
    (g : RestrictScalars A T Q →ₗ[A] RestrictScalars A T P)
    (u : RestrictScalars A T P →ₗ[A] RestrictScalars A S N)
    (v : RestrictScalars A S N →ₗ[A] RestrictScalars A T P)
    (hid : ∀ x : RestrictScalars A T P,
      g (f x) = RestrictScalars.lsmul A T P t x - v (u x)) :
    (PAdicCompletion.mapAddHom p T T (restrictScalarsUnderlyingAddHom g)).comp
        (PAdicCompletion.mapAddHom p T T (restrictScalarsUnderlyingAddHom f)) =
      p • AddMonoidHom.id (AdicCompletion (pAdicIdeal (A := T) p) P) -
        (PAdicCompletion.mapAddHom p S T (restrictScalarsUnderlyingAddHom v)).comp
          (PAdicCompletion.mapAddHom p T S (restrictScalarsUnderlyingAddHom u)) :=
  PAdicCompletion.mapAddHom_comp_eq_nsmul_sub p T T S _ _ _ _ _
    (underlyingAddHom_comp_eq_nsmul_sub p t ht f g u v hid)

/-- A positive-degree homotopy identity of `A`-linear maps, completed `p`-adically. -/
private theorem mapAddHom_underlying_add_comp_eq_nsmul_sub (p : ℕ) (t : T)
    (ht : ∀ x : RestrictScalars A T P, RestrictScalars.lsmul A T P t x = p • x)
    (f : RestrictScalars A T P →ₗ[A] RestrictScalars A T Q)
    (g : RestrictScalars A T Q →ₗ[A] RestrictScalars A T P)
    (f' : RestrictScalars A T P →ₗ[A] RestrictScalars A T Q')
    (g' : RestrictScalars A T Q' →ₗ[A] RestrictScalars A T P)
    (u : RestrictScalars A T P →ₗ[A] RestrictScalars A S N)
    (v : RestrictScalars A S N →ₗ[A] RestrictScalars A T P)
    (hid : ∀ x : RestrictScalars A T P,
      g (f x) + g' (f' x) = RestrictScalars.lsmul A T P t x - v (u x)) :
    (PAdicCompletion.mapAddHom p T T (restrictScalarsUnderlyingAddHom g)).comp
        (PAdicCompletion.mapAddHom p T T (restrictScalarsUnderlyingAddHom f)) +
        (PAdicCompletion.mapAddHom p T T (restrictScalarsUnderlyingAddHom g')).comp
          (PAdicCompletion.mapAddHom p T T (restrictScalarsUnderlyingAddHom f')) =
      p • AddMonoidHom.id (AdicCompletion (pAdicIdeal (A := T) p) P) -
        (PAdicCompletion.mapAddHom p S T (restrictScalarsUnderlyingAddHom v)).comp
          (PAdicCompletion.mapAddHom p T S (restrictScalarsUnderlyingAddHom u)) :=
  PAdicCompletion.mapAddHom_add_comp_eq_nsmul_sub p T T S T _ _ _ _ _ _ _
    (underlyingAddHom_add_comp_eq_nsmul_sub p t ht f g f' g' u v hid)

end UnderlyingIdentities

/-! ### `D ⟶ D'` is a split injection of `D`-modules -/

namespace PthRootExtension

section SplitInjection

variable (B : DividedPowerRing.{u}) (p : ℕ) (lam : (B : Type u)) [Nontrivial (XiAlg B)]

/-- `D`, the `p`-adic completion of the base ring `B`. -/
abbrev completedBaseRing : Type u :=
  AdicCompletion (pAdicIdeal (A := (B : Type u)) p) (B : Type u)

/-- **`D'`, the ring of [Stacks, Tag 07N1]**: the `p`-adic completion of
`B' = B[z]⟨ξ⟩/(ξ - (z^p - λ))`, taken along `(p) ⊆ B` so that it is visibly a module over `D`.
By `Crystalline.PAdicCompletion.coe_pow_smul_top_eq` the levels are the subgroups `pⁿ ·`
whichever of `B` and `B'` the ideal is read in, so this is the `p`-adic completion of the ring
`B'`, which is what the source's `D'` is. -/
abbrev completedPrimeRing : Type u :=
  AdicCompletion (pAdicIdeal (A := (B : Type u)) p) (primeRing B p lam)

/-- **The map `D ⟶ D'`**, the `p`-adic completion of the structure map `B → B'`. -/
abbrev completedToPrimeRing :
    completedBaseRing B p →ₗ[completedBaseRing B p] completedPrimeRing B p lam :=
  AdicCompletion.map (pAdicIdeal (A := (B : Type u)) p)
    (Algebra.linearMap (B : Type u) (primeRing B p lam))

/-- **The retraction of `D ⟶ D'`**, the `p`-adic completion of
`Crystalline.PthRootExtension.primeRetraction`, the coordinate of the basis vector
`z^0 ξ^[0] = 1` of the free `B`-module `B'`. -/
abbrev completedPrimeRetraction (hp : p ≠ 0) :
    completedPrimeRing B p lam →ₗ[completedBaseRing B p] completedBaseRing B p :=
  AdicCompletion.map (pAdicIdeal (A := (B : Type u)) p) (primeRetraction B p lam hp)

/-- **`D ⟶ D'` is split as a map of `D`-modules**, the `p`-adic completion of
`Crystalline.PthRootExtension.primeRetraction_comp`.  This is the step of the proof of
[Stacks, Tag 07N1] which reads "`D'` is the `p`-adic completion of the free `D`-module
`⨁ z^i ξ^[n] D`, so `D → D'` has a continuous `D`-linear section"; completion is functorial for
linear maps, so the uncompleted retraction completes to a retraction. -/
theorem completedPrimeRetraction_comp_completedToPrimeRing (hp : p ≠ 0) :
    (completedPrimeRetraction B p lam hp) ∘ₗ (completedToPrimeRing B p lam) = LinearMap.id := by
  show (AdicCompletion.map (pAdicIdeal (A := (B : Type u)) p) (primeRetraction B p lam hp)) ∘ₗ
      (AdicCompletion.map (pAdicIdeal (A := (B : Type u)) p)
        (Algebra.linearMap (B : Type u) (primeRing B p lam))) = LinearMap.id
  rw [AdicCompletion.map_comp, primeRetraction_comp, AdicCompletion.map_id]

/-- **`D ⟶ D'` is injective**, being split. -/
theorem injective_completedToPrimeRing (hp : p ≠ 0) :
    Function.Injective (completedToPrimeRing B p lam) :=
  Function.LeftInverse.injective (g := completedPrimeRetraction B p lam hp) fun x ↦
    DFunLike.congr_fun (completedPrimeRetraction_comp_completedToPrimeRing B p lam hp) x

end SplitInjection

/-! ### The two completed de Rham complexes of the extension -/

section CompletedComplexes

variable (A : Type u) [CommRing A] (B : DividedPowerRing.{u}) [Algebra A (B : Type u)] (p : ℕ)
  (lam : (B : Type u)) (hp : p ≠ 0) (M : Type w) [AddCommGroup M] [Module (B : Type u) M]

/-- The degree-`q` term `M ⊗_B Ω^q_{B/A,γ}` of the de Rham complex of the base. -/
abbrev baseDeRhamTerm (q : ℕ) : Type (max u w) :=
  M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))

/-- The degree-`q` term `M' ⊗_{B'} Ω^q_{B'/A,γ'}` of the de Rham complex of the extension, with
`M' = B' ⊗_B M`. -/
abbrev primeDeRhamTerm (q : ℕ) : Type (max u w) :=
  (primeRing B p lam ⊗[(B : Type u)] M) ⊗[primeRing B p lam]
    (⋀[primeRing B p lam]^q (primeForms A B p lam hp))

/-- **The degree-`q` term of the `p`-adically completed de Rham complex of the base**, the
completion of `M ⊗_B Ω^q_{B/A,γ}` along `(p) ⊆ B`. -/
abbrev completedBaseDeRhamTerm (q : ℕ) : Type (max u w) :=
  AdicCompletion (pAdicIdeal (A := (B : Type u)) p) (baseDeRhamTerm A B M q)

/-- **The degree-`q` term of the `p`-adically completed de Rham complex of the extension**, the
completion of `M' ⊗_{B'} Ω^q_{B'/A,γ'}` along `(p) ⊆ B'`. -/
abbrev completedPrimeDeRhamTerm (q : ℕ) : Type (max u w) :=
  AdicCompletion (pAdicIdeal (A := primeRing B p lam) p) (primeDeRhamTerm A B p lam hp M q)

/-- The differential of the de Rham complex of the base in degree `q`, the extension of `∇` to
`M ⊗_B ⋀^q Ω¹_{B/A,γ}` of [Stacks, Tag 07I0], read as an additive map. -/
abbrev baseDeRhamDifferential (S : SourceDeRham A (B : Type u))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M) (q : ℕ) :
    baseDeRhamTerm A B M q →+ baseDeRhamTerm A B M (q + 1) :=
  restrictScalarsUnderlyingAddHom
    ((extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
      (baseFormsGenerationHypothesis A B S) nabla).toLinearMap q)

/-- The base change of `∇` along the comparison `ψ : Ω¹_{B/A,γ} → Ω¹_{B'/A,γ'}`, the connection
on `M' = B' ⊗_B M` which the de Rham complex of the extension is built from. -/
abbrev primeConnection (nabla : Connection A (B : Type u) (baseFormsProjection A B) M) :=
  Connection.baseChange (primeFormsComparison A B p lam hp) nabla
    (primeFormsComparison_dividedPowerDifferential A B p lam hp)

/-- The differential of the de Rham complex of the extension in degree `q`, read as an additive
map. -/
abbrev primeDeRhamDifferential (S' : SourceDeRham A (primeRing B p lam))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M) (q : ℕ) :
    primeDeRhamTerm A B p lam hp M q →+ primeDeRhamTerm A B p lam hp M (q + 1) :=
  restrictScalarsUnderlyingAddHom
    ((extendedConnection S' (primeFormsProjection A B p lam hp) (Submodule.mkQ_surjective _)
      (primeFormsGenerationHypothesis A B p lam hp S')
      (primeConnection A B p lam hp M nabla)).toLinearMap q)

/-- **The differential of the completed de Rham complex of the base**, the `p`-adic completion of
`Crystalline.PthRootExtension.baseDeRhamDifferential`.

It is an additive map, not a `B`-linear one: the extended connection is `A`-linear and the
Leibniz rule forbids `B`-linearity, so `AdicCompletion.map` of it over `B` does not exist and
`Crystalline.PAdicCompletion.mapAddHom` is what replaces it. -/
abbrev completedBaseDeRhamDifferential (S : SourceDeRham A (B : Type u))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M) (q : ℕ) :
    completedBaseDeRhamTerm A B p M q →+ completedBaseDeRhamTerm A B p M (q + 1) :=
  PAdicCompletion.mapAddHom p (B : Type u) (B : Type u) (baseDeRhamDifferential A B M S nabla q)

/-- **The differential of the completed de Rham complex of the extension**, the `p`-adic
completion of `Crystalline.PthRootExtension.primeDeRhamDifferential`. -/
abbrev completedPrimeDeRhamDifferential (S' : SourceDeRham A (primeRing B p lam))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M) (q : ℕ) :
    completedPrimeDeRhamTerm A B p lam hp M q →+ completedPrimeDeRhamTerm A B p lam hp M (q + 1) :=
  PAdicCompletion.mapAddHom p (primeRing B p lam) (primeRing B p lam)
    (primeDeRhamDifferential A B p lam hp M S' nabla q)

/-- **The completed comparison `ĉ_M^•`**, the `p`-adic completion of the canonical map of de Rham
complexes `c_M^•` of [Stacks, Lemma 60.6.9, Tag 07HW]. -/
abbrev completedComparisonMap
    (c : ∀ q : ℕ,
      RestrictScalars A (B : Type u) (baseDeRhamTerm A B M q) →ₗ[A]
        RestrictScalars A (primeRing B p lam) (primeDeRhamTerm A B p lam hp M q))
    (q : ℕ) :
    completedBaseDeRhamTerm A B p M q →+ completedPrimeDeRhamTerm A B p lam hp M q :=
  PAdicCompletion.mapAddHom p (B : Type u) (primeRing B p lam)
    (restrictScalarsUnderlyingAddHom (c q))

end CompletedComplexes

end PthRootExtension

/-! ### Tag 07N1 over the `p`-adic completions -/

open PthRootExtension

/-- **Tag 07N1 for the `p`-adic completions of the de Rham complexes of the extension
`B → B[z]⟨ξ⟩/(ξ - (z^p - λ))`.**

With the hypotheses of
`Crystalline.exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials` and nothing
beyond them, the `p`-adic completion `ĉ_M^•` of the canonical map of de Rham complexes admits an
additive map `ê_M^•` of the completed complexes in the opposite direction which commutes with the
completed differentials, together with completed homotopies `ĥ` and `k̂` exhibiting `ĉ ∘ ê` and
`ê ∘ ĉ` as homotopic to multiplication by `p`.  The same conclusion with the three maps linear
over the completed base is
`Crystalline.exists_completedLinearHomotopyInverse_pthRootExtension_dividedPowerDifferentials`.

Every map in the conclusion is the completion of its uncompleted counterpart and every identity
is the image of the uncompleted identity under one additive functor: the three shapes involved
are a commuting square, a degree-zero homotopy identity and a positive-degree homotopy identity,
transported by `Crystalline.PAdicCompletion.mapAddHom_comp_eq_comp`,
`Crystalline.PAdicCompletion.mapAddHom_comp_eq_nsmul_sub` and
`Crystalline.PAdicCompletion.mapAddHom_add_comp_eq_nsmul_sub`.

These are the completions of the complexes of the uncompleted `B'`; the tag itself is
`Crystalline.PthRootExtension.exists_homotopyInverse_completedPthRootExtension`. -/
theorem exists_completedHomotopyInverse_pthRootExtension_dividedPowerDifferentials
    {A : Type u} {M : Type w} [CommRing A]
    (B : DividedPowerRing.{u}) (p : ℕ) (lam : (B : Type u)) (hp : p ≠ 0)
    [Algebra A (B : Type u)]
    [Nontrivial (XiAlg B)] [Fact p.Prime]
    [Algebra (IntegersAtPrime p) (B : Type u)]
    [AddCommGroup M] [Module (B : Type u) M]
    (S : SourceDeRham A (B : Type u))
    (S' : SourceDeRham A (primeRing B p lam))
    (nabla : Connection A (B : Type u) (baseFormsProjection A B) M)
    (hintegrable : Connection.IsIntegrable S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
      (baseFormsGenerationHypothesis A B S) nabla)
    (c : ∀ q : ℕ,
      RestrictScalars A (B : Type u) (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B))) →ₗ[A]
        RestrictScalars A (primeRing B p lam)
          ((primeRing B p lam ⊗[(B : Type u)] M)
            ⊗[primeRing B p lam]
              (⋀[primeRing B p lam]^q (primeForms A B p lam hp))))
    (hc_wedge : ∀ (q : ℕ) (m : M) (omega : Fin q → (baseForms A B)),
      c q (m ⊗ₜ[(B : Type u)] exteriorPower.ιMulti (B : Type u) q omega) =
        (1 ⊗ₜ[(B : Type u)] m) ⊗ₜ[primeRing B p lam]
          exteriorPower.ιMulti (primeRing B p lam) q ((primeFormsComparison A B p lam hp) ∘ omega))
    (hc_comm : ∀ (q : ℕ) (x : RestrictScalars A (B : Type u)
        (M ⊗[(B : Type u)] (⋀[(B : Type u)]^q (baseForms A B)))),
      c (q + 1)
          ((extendedConnection S (baseFormsProjection A B) (Submodule.mkQ_surjective _)
            (baseFormsGenerationHypothesis A B S) nabla).toLinearMap q x) =
        (extendedConnection S' (primeFormsProjection A B p lam hp) (Submodule.mkQ_surjective _)
          (primeFormsGenerationHypothesis A B p lam hp S')
          (Connection.baseChange (primeFormsComparison A B p lam hp) nabla
            (primeFormsComparison_dividedPowerDifferential A B p lam hp))).toLinearMap q (c q x)) :
    ∃ ehat : ∀ q : ℕ,
      completedPrimeDeRhamTerm A B p lam hp M q →+ completedBaseDeRhamTerm A B p M q,
      (∀ q : ℕ, (ehat (q + 1)).comp
            (completedPrimeDeRhamDifferential A B p lam hp M S' nabla q) =
          (completedBaseDeRhamDifferential A B p M S nabla q).comp (ehat q)) ∧
        (∃ hhat : ∀ q : ℕ,
            completedPrimeDeRhamTerm A B p lam hp M (q + 1) →+
              completedPrimeDeRhamTerm A B p lam hp M q,
          ((hhat 0).comp (completedPrimeDeRhamDifferential A B p lam hp M S' nabla 0) =
              (p : ℕ) • AddMonoidHom.id (completedPrimeDeRhamTerm A B p lam hp M 0) -
                (completedComparisonMap A B p lam hp M c 0).comp (ehat 0)) ∧
            ∀ q : ℕ,
              (completedPrimeDeRhamDifferential A B p lam hp M S' nabla q).comp (hhat q) +
                  (hhat (q + 1)).comp
                    (completedPrimeDeRhamDifferential A B p lam hp M S' nabla (q + 1)) =
                (p : ℕ) • AddMonoidHom.id (completedPrimeDeRhamTerm A B p lam hp M (q + 1)) -
                  (completedComparisonMap A B p lam hp M c (q + 1)).comp (ehat (q + 1))) ∧
        (∃ khat : ∀ q : ℕ,
            completedBaseDeRhamTerm A B p M (q + 1) →+ completedBaseDeRhamTerm A B p M q,
          ((khat 0).comp (completedBaseDeRhamDifferential A B p M S nabla 0) =
              (p : ℕ) • AddMonoidHom.id (completedBaseDeRhamTerm A B p M 0) -
                (ehat 0).comp (completedComparisonMap A B p lam hp M c 0)) ∧
            ∀ q : ℕ,
              (completedBaseDeRhamDifferential A B p M S nabla q).comp (khat q) +
                  (khat (q + 1)).comp
                    (completedBaseDeRhamDifferential A B p M S nabla (q + 1)) =
                (p : ℕ) • AddMonoidHom.id (completedBaseDeRhamTerm A B p M (q + 1)) -
                  (ehat (q + 1)).comp (completedComparisonMap A B p lam hp M c (q + 1))) :=
  Exists.elim (exists_homotopyInverse_pthRootExtension_dividedPowerDifferentials B p lam hp S S'
      nabla hintegrable c hc_wedge hc_comm) fun e he ↦
    Exists.elim he.2.1 fun h hh ↦
      Exists.elim he.2.2 fun k hk ↦
        ⟨fun q ↦ PAdicCompletion.mapAddHom p (primeRing B p lam) (B : Type u)
            (restrictScalarsUnderlyingAddHom (e q)),
          fun q ↦ PAdicCompletion.mapAddHom_comp_eq_comp p (primeRing B p lam)
            (primeRing B p lam) (B : Type u) (B : Type u)
            (primeDeRhamDifferential A B p lam hp M S' nabla q)
            (restrictScalarsUnderlyingAddHom (e (q + 1)))
            (restrictScalarsUnderlyingAddHom (e q)) (baseDeRhamDifferential A B M S nabla q)
            (AddMonoidHom.ext fun y ↦ he.1 q y),
          ⟨fun q ↦ PAdicCompletion.mapAddHom p (primeRing B p lam) (primeRing B p lam)
              (restrictScalarsUnderlyingAddHom (h q)),
            mapAddHom_underlying_comp_eq_nsmul_sub p
              (algebraMap (B : Type u) (primeRing B p lam) ((p : ℕ) : (B : Type u)))
              (restrictScalars_lsmul_algebraMap_natCast A (B : Type u) (primeRing B p lam) p)
              _ (h 0) (e 0) (c 0) hh.1,
            fun q ↦ mapAddHom_underlying_add_comp_eq_nsmul_sub p
              (algebraMap (B : Type u) (primeRing B p lam) ((p : ℕ) : (B : Type u)))
              (restrictScalars_lsmul_algebraMap_natCast A (B : Type u) (primeRing B p lam) p)
              (h q) _ _ (h (q + 1)) (e (q + 1)) (c (q + 1)) (hh.2 q)⟩,
          ⟨fun q ↦ PAdicCompletion.mapAddHom p (B : Type u) (B : Type u)
              (restrictScalarsUnderlyingAddHom (k q)),
            mapAddHom_underlying_comp_eq_nsmul_sub p ((p : ℕ) : (B : Type u))
              (restrictScalars_lsmul_natCast A (B : Type u) p) _ (k 0) (c 0) (e 0) hk.1,
            fun q ↦ mapAddHom_underlying_add_comp_eq_nsmul_sub p ((p : ℕ) : (B : Type u))
              (restrictScalars_lsmul_natCast A (B : Type u) p) (k q) _ _ (k (q + 1))
              (c (q + 1)) (e (q + 1)) (hk.2 q)⟩⟩

end Crystalline

end
