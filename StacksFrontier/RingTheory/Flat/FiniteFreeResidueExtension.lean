module

import Mathlib.Algebra.Field.ULift
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
import StacksFrontier.RingTheory.Flat.LocalConstruction
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Constructing flat ring maps

Two ways of realizing a prescribed residue field extension by a flat ring map.

The first (Stacks Tag 07NE) is finite free, and realizes a *finite* extension: for a commutative
ring `R`, a prime ideal `p ⊆ R` and a finite extension `L / κ(p)` of the residue field of `R` at
`p`, there are a commutative ring `S` and a finite free ring map `φ : R →+* S` such that `q := pS`
is prime, lies over `p`, and whose induced residue field extension `κ(q) / κ(p)` is isomorphic to
`L / κ(p)`.

The second (Stacks Tag 03C3) realizes an *arbitrary* extension, at the price of finite freeness:
for a local ring `(R, 𝔪, k)` and a field extension `K / k` there are a local ring `(R', 𝔪', k')`,
a flat local ring map `R → R'` with `𝔪' = 𝔪 R'`, and an isomorphism `k' ≅ K` of extensions of
`k`. So every extension of the residue field of a local ring is realized, with no change to the
maximal ideal, by a flat local extension of the ring itself.

## Main definitions

* `ResidueFieldAtPrime R p`: the residue field `κ(p)` of `R` at `p`; an abbreviation for
  `Ideal.ResidueField p`.
* `inducedResidueMap φ p q h`: the residue field extension `κ(p) →+* κ(q)` induced by
  `φ : R →+* S` at a prime `q` lying over `p`; `Ideal.ResidueField.map p q φ h`.
* `IsFiniteFree φ`: the ring map `φ : R →+* S` is finite free, i.e. `S` regarded as an
  `R`-module via `φ` is free of finite rank.
* `adjoinRootFracHom K g`: the base change of `AdjoinRoot g` along `algebraMap D K`, the ring
  map `AdjoinRoot g →+* AdjoinRoot (g.map (algebraMap D K))` fixing `D` and sending root to root.

## Main results

* `exists_isFiniteFree_residueField_equiv`: a finite extension of `κ(p)` is the residue field
  extension of a finite free
  ring map `R → S` at `q = pS`.
* `isFractionRing_adjoinRootFrac`: for `g` monic over a domain `D` whose image over `K = Frac D`
  is irreducible, the field `AdjoinRoot (g.map (algebraMap D K))` is a fraction field of the
  domain `AdjoinRoot g`.
* `IsLocalRing.exists_flat_residueField_algEquiv`: for a local ring `R` and a field extension `K`
  of its residue field there is a flat local `R`-algebra `R'` with `𝔪 R'` for its maximal ideal
  and with residue field `k`-isomorphic to `K`.

## Implementation notes

*The finite free case.* The extension `L / κ(p)` is encoded by `[Algebra (κ(p)) L]`, with
structure map `algebraMap (κ(p)) L`; the ideal `pS` is `Ideal.map φ p`; and "isomorphic as an
extension of `κ(p)`" means that the field isomorphism `Φ : κ(q) ≃+* L` satisfies
`Φ ∘ inducedResidueMap φ p q = algebraMap (κ(p)) L`.

*The general case is a transfinite assembly of monogenic steps.* The construction, which is no
part of the statement of 03C3, adjoins the elements of `K` one at a time. A monogenic step
`κ ⊆ κ(α)` over a local ring `(A, 𝔪_A, κ)` is realized by `A[x]` localized at the prime
`𝔪_A A[x]` when `α` is transcendental over `κ` (the residue field there is `κ(x)`), and by
`A[T] / (T ^ d + ∑ λ_i T ^ (d - i))` for a lift of the minimal polynomial of `α` when `α` is
algebraic over `κ`; a directed colimit of such extensions is again one, because flatness and the
formation of `𝔪 · (-)` both commute with directed colimits. Those steps and colimits are carried
out in `StacksFrontier/RingTheory/Flat/LocalConstruction.lean`, whose bookkeeping object is
`GoodLift A F`: a flat local `A`-algebra with `𝔪_{A'} = 𝔪_A A'` together with a `κ`-embedding
`ResidueField A' →+* F`. A good lift whose embedding is onto solves the problem.

*The recursion is categorical, not a well-founded recursion on the index.* A hand-rolled
recursion cannot state its own coherence: the transition map from stage `j` to stage `i` has a
type depending on the good lifts constructed at `j` and `i`, so the tower and the cocycle of its
legs have to be built simultaneously. Organizing good lifts into a category makes a coherent
directed system a functor and the cocycle functoriality, and Mathlib's transfinite iteration
`CategoryTheory.SmallObject.SuccStruct.iterationFunctor` then supplies the tower, including its
definition at limit stages. Morphisms of good lifts are not required to be flat: flatness of each
stage over the base is part of `GoodLift`, and the colimit engine asks only that the transition
maps be local, so morphisms compose without any flatness input.

*The local ring map of 03C3 is an algebra map.* The source's `R → R'` is `algebraMap R R'`, being
local is `IsLocalHom` and being flat is `Module.Flat R R'`; the `Algebra R R'`, `IsLocalRing R'`
and `IsLocalHom` binders are the lemma's preamble ("there exists a local ring and a local ring
map"), and the three conjuncts are flatness, `𝔪' = 𝔪 R'`, and `k' ≅ K` over `k`. No hypothesis
is imposed on `K / k`: it need not be algebraic, finitely generated or separable.

*`𝔪' = 𝔪 R'` and `k' ≅ K` are two conjuncts, not one.* `𝔪 R'` is
`(maximalIdeal R).map (algebraMap R R')`, and a local ring map always has `𝔪 R' ≤ 𝔪'`, so the
second conjunct is the assertion that `R' / 𝔪 R'` is already a field. Granted it, the third
conjunct is exactly that this field is `K` as an extension of `k`; the two are therefore
equivalent to the single statement that the closed fibre `k ⊗[R] R'` is `k`-isomorphic to `K`,
and are kept separate because that is the form in which the source and its users state them.

*Isomorphic as an extension of `k`.* `ResidueField R' ≃ₐ[ResidueField R] K` is an isomorphism of
`k`-algebras for the canonical `k`-algebra structure on `k'` induced by `algebraMap R R'`
(`IsLocalRing.ResidueField.instAlgebra`), so an abstract ring isomorphism `k' ≅ K` that does not
respect the two maps out of `k` does not satisfy it. Since a `k`-algebra map of fields is
injective, "isomorphic as an extension of `k`" and "`K` embeds in `k'` over `k` by a surjection"
are the same requirement, and the `≃ₐ` form is the usable one.

*The universes of 03C3.* `R : Type u` and `K : Type v` are independent and `R' : Type (max u v)`,
which is where the construction lands: it adjoins one element of `K` at a time to `R`, so `R'` has
cardinality at most `max #R #K ℵ₀`. The source states the lemma with `R` and `K` in one universe,
which is the case `v = u`. Since `GoodLift` is universe-monomorphic, the assembly is run over
`ULift.{v} R` and `ULift.{u} K` and its conclusion transported back along `ULift.ringEquiv`.

## References

* [StacksProject 07NE](https://stacks.math.columbia.edu/tag/07NE)
* [StacksProject 03C3](https://stacks.math.columbia.edu/tag/03C3)
* [StacksProject 09E0](https://stacks.math.columbia.edu/tag/09E0), the separable algebraic case
  of 03C3 as a colimit of finite étale extensions

## Tags

flat, flat ring map, flat local ring map, finite free, local ring, residue field,
field extension, monogenic extension
-/

@[expose] public section

open IsLocalRing

/-- The residue field `κ(p)` of `R` at the prime `p`: Mathlib's `Ideal.ResidueField p`, the
residue field of the local ring `Localization.AtPrime p`. -/
@[ega "0 21.9.8", ega "I 1.1.1", sga "1 I 7.5" "more general"]
abbrev ResidueFieldAtPrime (R : Type*) [CommRing R] (p : Ideal R) [p.IsPrime] : Type _ :=
  p.ResidueField

/-- The residue field extension `κ(p) → κ(q)` induced by `φ` at a prime `q` of `S` lying over
`p`, i.e. with `p = q.comap φ`: an opaque wrapper for `Ideal.ResidueField.map p q φ h`, because
the reducible Mathlib abbrev makes the composition statement time out at `whnf`. Mathlib's is a
`reducible abbrev` with this very body, and `inducedResidueMap_comp` spelled with it does not
elaborate at all — `(deterministic) timeout at whnf`, still at a million heartbeats — while over
the opaque `def` it elaborates instantly. -/
@[ega "0 1.0.7", ega "I 1.2.1"]
noncomputable def inducedResidueMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (h : p = q.comap φ) :
    ResidueFieldAtPrime R p →+* ResidueFieldAtPrime S q :=
  ResidueField.map (Localization.localRingHom p q φ h)

/-- The residue field extension induced by the identity ring map is the identity. -/
theorem inducedResidueMap_id {R : Type*} [CommRing R] (p : Ideal R) [p.IsPrime]
    (h : p = p.comap (RingHom.id R)) :
    inducedResidueMap (RingHom.id R) p p h = RingHom.id (ResidueFieldAtPrime R p) := by
  simp [inducedResidueMap, Localization.localRingHom_id]

/-- **Functoriality.** The residue field extension induced by a composite `ψ ∘ φ` is the
composite of the induced extensions, at a chain of primes `p = q.comap φ`, `q = r.comap ψ`. -/
theorem inducedResidueMap_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime]
    (r : Ideal T) [r.IsPrime] (hpq : p = q.comap φ) (hqr : q = r.comap ψ)
    (hpr : p = r.comap (ψ.comp φ)) :
    inducedResidueMap (ψ.comp φ) p r hpr
      = (inducedResidueMap ψ q r hqr).comp (inducedResidueMap φ p q hpq) := by
  unfold inducedResidueMap
  rw [← ResidueField.map_comp]
  congr 1
  exact Localization.localRingHom_comp p q r φ hpq ψ hqr

/-- The residue field extension induced by `φ` sends the residue class of `c : R` to the residue
class of `φ c`. -/
theorem inducedResidueMap_algebraMap {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (p : Ideal R) [p.IsPrime] (q : Ideal S) [q.IsPrime] (hpq : p = q.comap φ) (c : R) :
    inducedResidueMap φ p q hpq (algebraMap R (ResidueFieldAtPrime R p) c)
      = algebraMap (S ⧸ q) (ResidueFieldAtPrime S q) (Ideal.Quotient.mk q (φ c)) :=
  Ideal.ResidueField.map_algebraMap p q φ hpq c

/-- A ring map `φ : R →+* S` is finite free if `S`, regarded as an `R`-module via `φ`, is
free of finite rank. -/
def IsFiniteFree {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) : Prop :=
  letI := φ.toAlgebra
  Module.Free R S ∧ Module.Finite R S

/-- The identity ring map is finite free. -/
theorem isFiniteFree_id (R : Type*) [CommRing R] : IsFiniteFree (RingHom.id R) :=
  ⟨Module.Free.self R, Module.Finite.self R⟩

/-- Finite free ring maps are closed under composition. -/
theorem isFiniteFree_comp {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    (φ : R →+* S) (ψ : S →+* T) (hφ : IsFiniteFree φ) (hψ : IsFiniteFree ψ) :
    IsFiniteFree (ψ.comp φ) := by
  let := φ.toAlgebra; let := ψ.toAlgebra; let := (ψ.comp φ).toAlgebra
  have : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun _ => rfl
  obtain ⟨_, _⟩ := hφ
  obtain ⟨_, _⟩ := hψ
  exact ⟨.trans (R := R) (S := S) (M := T), .trans (R := R) S T⟩

/-- For a monic polynomial `f` over `R`, the structure map `R → AdjoinRoot f` is finite free. -/
@[ega "0 10.3.1.2" "more general", ega "0 22.4.1" "(i), special case"]
theorem isFiniteFree_adjoinRoot_of (R : Type*) [CommRing R] (f : Polynomial R)
    (hf : f.Monic) : IsFiniteFree (AdjoinRoot.of f) := by
  have halg : (AdjoinRoot.of f).toAlgebra = (inferInstance : Algebra R (AdjoinRoot f)) :=
    Algebra.algebra_ext _ _ fun r => by
      rw [RingHom.algebraMap_toAlgebra, AdjoinRoot.algebraMap_eq]
  rw [IsFiniteFree, halg]
  exact ⟨.of_basis (AdjoinRoot.powerBasis' hf).basis, (AdjoinRoot.powerBasis' hf).finite⟩

/-! ### The conclusion as a predicate, and the two reduction steps -/

/-- The conclusion of Stacks 07NE for the data `(R, p, L)`: there is a finite free `φ : R →+* S`
with `q := pS` prime, lying over `p`, and a `κ(p)`-algebra isomorphism `κ(q) ≃ L`. Packaging the
conclusion as a `Prop` lets the recursion on the degree `[L : κ(p)]` quantify over the ambient
ring, prime and base field, all three of which change at the intermediate-field step. -/
public def Stacks07NEConcl.{u, v} (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (L : Type v) [Field L] [Algebra (ResidueFieldAtPrime R p) L] : Prop :=
  ∃ (S : Type u) (_ : CommRing S) (φ : R →+* S),
    IsFiniteFree φ ∧
    ∃ (_ : (Ideal.map φ p).IsPrime) (hpq : p = (Ideal.map φ p).comap φ),
      ∃ (Φ : ResidueFieldAtPrime S (Ideal.map φ p) ≃+* L),
        (Φ.toRingHom.comp (inducedResidueMap φ p (Ideal.map φ p) hpq) :
          ResidueFieldAtPrime R p →+* L) = algebraMap (ResidueFieldAtPrime R p) L

/-- If `algebraMap κ(p) L` is bijective and the prime `q` equals `p`, then `κ(q) ≃+* L`
compatibly with the map `κ(p) → κ(q)` induced by the identity of `R`.

Taking `q` and `[q.IsPrime]` as parameters is what lets `Ideal.map (RingHom.id R) p` be
substituted for `p` in a goal that also carries its primality instance. -/
public theorem exists_residueFieldEquiv_of_eq (R : Type*) [CommRing R] (p : Ideal R) [p.IsPrime]
    (L : Type*) [Field L] [Algebra (ResidueFieldAtPrime R p) L]
    (hbij : Function.Bijective (algebraMap (ResidueFieldAtPrime R p) L))
    (q : Ideal R) [q.IsPrime] (hq : q = p) (hpq : p = q.comap (RingHom.id R)) :
    ∃ Φ : ResidueFieldAtPrime R q ≃+* L,
      (Φ.toRingHom.comp (inducedResidueMap (RingHom.id R) p q hpq) :
        ResidueFieldAtPrime R p →+* L) = algebraMap (ResidueFieldAtPrime R p) L := by
  subst hq
  exact ⟨RingEquiv.ofBijective _ hbij, by rw [inducedResidueMap_id, RingHom.comp_id]; rfl⟩

/-- **Base case.** If `[L : κ(p)] ≤ 1` then `algebraMap κ(p) L` is an isomorphism, and
`S = R`, `φ = RingHom.id R` witness the conclusion. -/
public theorem exists_isFiniteFree_residueFieldEquiv_of_finrank_le_one.{u, v}
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (L : Type v) [Field L] [Algebra (ResidueFieldAtPrime R p) L]
    [Module.Finite (ResidueFieldAtPrime R p) L]
    (hd : Module.finrank (ResidueFieldAtPrime R p) L ≤ 1) :
    Stacks07NEConcl R p L := by
  have hbij : Function.Bijective (algebraMap (ResidueFieldAtPrime R p) L) := by
    rw [Algebra.bijective_algebraMap_iff]
    exact (Subalgebra.bot_eq_top_of_finrank_eq_one (le_antisymm hd Module.finrank_pos)).symm
  have hmap : Ideal.map (RingHom.id R) p = p := Ideal.map_id p
  have hqp : (Ideal.map (RingHom.id R) p).IsPrime := by rw [hmap]; infer_instance
  have hpq : p = (Ideal.map (RingHom.id R) p).comap (RingHom.id R) := by
    rw [hmap, Ideal.comap_id]
  exact ⟨R, inferInstance, RingHom.id R, isFiniteFree_id R, hqp, hpq,
    exists_residueFieldEquiv_of_eq R p L hbij _ hmap hpq⟩

/-! ### The monogenic step

The construction takes `S₁ = AdjoinRoot f`, `φ₁ = AdjoinRoot.of f`, for a monic `f ∈ R[X]`
whose reduction over `K = κ(p)` is the minimal polynomial of a denominator-cleared generator
`β` of the simple subextension `K⟮α⟯ = K⟮β⟯`. -/

/-- **Denominator-cleared monic lift.** For `α : L` and `K = κ(p)` there are a generator
`β : L` of the same simple subextension, `K⟮β⟯ = K⟮α⟯`, and a monic `f ∈ R[X]` whose
coefficientwise reduction along `algebraMap R K` is `minpoly K β`.

Write the coefficients of `minpoly K α` as fractions over `R ⧸ p` with a common denominator
`s`, and put `β = s • α`. Then `minpoly K β` is `minpoly K α` with its roots scaled by `s`, which
clears the denominators: its coefficients all lie in the range of `algebraMap R K`, so it lifts
to a monic `f ∈ R[X]`. -/
theorem exists_monic_lift_minpoly.{u, v} (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (L : Type v) [Field L] [Algebra (ResidueFieldAtPrime R p) L]
    [Module.Finite (ResidueFieldAtPrime R p) L]
    (α : L) :
    ∃ (β : L) (f : Polynomial R),
      f.Monic ∧
      IntermediateField.adjoin (ResidueFieldAtPrime R p) {β} =
        IntermediateField.adjoin (ResidueFieldAtPrime R p) {α} ∧
      f.map (algebraMap R (ResidueFieldAtPrime R p))
        = minpoly (ResidueFieldAtPrime R p) β := by
  classical
  set K := ResidueFieldAtPrime R p
  set D := R ⧸ p
  have hα : IsIntegral K α := Algebra.IsIntegral.isIntegral α
  set m := minpoly K α
  set d := m.natDegree with hd_def
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors D)
    (Finset.range (d + 1)) (fun i => m.coeff i)
  set s : D := (b : D)
  set c : K := algebraMap D K s with hc_def
  have hc_ne : c ≠ 0 := by
    rw [hc_def]
    exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  set β := algebraMap K L c * α with hβ_def
  have hβint : IsIntegral K β := IsIntegral.mul isIntegral_algebraMap hα
  have hmin_β : minpoly K β = m.scaleRoots c := by
    rw [hβ_def, ← Algebra.smul_def]
    exact IsIntegrallyClosed.minpoly_smul hc_ne hα
  have hαeq : algebraMap K L c⁻¹ * β = α := by
    rw [hβ_def, ← mul_assoc, ← map_mul, inv_mul_cancel₀ hc_ne, map_one, one_mul]
  have hadj : IntermediateField.adjoin K {β} = IntermediateField.adjoin K {α} := by
    refine le_antisymm ?_ ?_
    · rw [IntermediateField.adjoin_simple_le_iff, hβ_def]
      exact mul_mem (IntermediateField.algebraMap_mem _ c)
        (IntermediateField.mem_adjoin_simple_self K α)
    · rw [IntermediateField.adjoin_simple_le_iff, ← hαeq]
      exact mul_mem (IntermediateField.algebraMap_mem _ c⁻¹)
        (IntermediateField.mem_adjoin_simple_self K β)
  have hc_mem : c ∈ (algebraMap D K).range := ⟨s, rfl⟩
  have hcoeff : ∀ n : ℕ, (minpoly K β).coeff n ∈ (algebraMap D K).range := by
    intro n
    rw [hmin_β, Polynomial.coeff_scaleRoots, ← hd_def]
    rcases lt_or_ge n d with hlt | hge
    · have hcmul : c * m.coeff n ∈ (algebraMap D K).range := by
        have hint := hb n (Finset.mem_range.mpr (by omega))
        rw [Algebra.smul_def, ← hc_def] at hint
        exact hint
      rw [show d - n = (d - n - 1) + 1 from by omega, pow_succ,
        show m.coeff n * (c ^ (d - n - 1) * c) = c * m.coeff n * c ^ (d - n - 1) from by ring]
      exact mul_mem hcmul (pow_mem hc_mem _)
    · rw [Nat.sub_eq_zero_of_le hge, pow_zero, mul_one]
      rcases eq_or_lt_of_le hge with heq | hgt
      · rw [← heq, hd_def, (minpoly.monic hα).coeff_natDegree]
        exact one_mem _
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [← hd_def]; omega)]
        exact zero_mem _
  have hrange : Set.range (algebraMap D K) = Set.range (algebraMap R K) :=
    ((Ideal.Quotient.mk_surjective (I := p)).range_comp (algebraMap D K)).symm
  have hlifts : minpoly K β ∈ Polynomial.lifts (algebraMap R K) := by
    refine (Polynomial.lifts_iff_coeff_lifts (minpoly K β)).mpr fun n => ?_
    rw [← hrange, ← RingHom.coe_range]
    exact hcoeff n
  obtain ⟨f, hfmap, _, hfmonic⟩ :=
    Polynomial.lifts_and_natDegree_eq_and_monic hlifts (minpoly.monic hβint)
  exact ⟨β, f, hfmonic, hadj, hfmap⟩

/-- The base change of `AdjoinRoot g` along `algebraMap D K`, i.e. `AdjoinRoot.map` for the
tautological divisibility: the `D`-algebra map
`AdjoinRoot g →+* AdjoinRoot (g.map (algebraMap D K))` sending `root g` to `root`. It is used
below with `K` the fraction field of a domain `D`, where it is injective for monic `g`. -/
noncomputable def adjoinRootFracHom {D : Type*} [CommRing D] (K : Type*) [Field K]
    [Algebra D K] (g : Polynomial D) :
    AdjoinRoot g →+* AdjoinRoot (Polynomial.map (algebraMap D K) g) :=
  AdjoinRoot.map (algebraMap D K) g _ dvd_rfl

open Polynomial in
/-- `adjoinRootFracHom` sends the class of `q` to the class of the coefficientwise image
of `q`. -/
theorem adjoinRootFracHom_mk {D : Type*} [CommRing D] (K : Type*) [Field K]
    [Algebra D K] (g : Polynomial D) (q : Polynomial D) :
    adjoinRootFracHom K g (AdjoinRoot.mk g q)
      = AdjoinRoot.mk (Polynomial.map (algebraMap D K) g) (Polynomial.map (algebraMap D K) q) := by
  unfold adjoinRootFracHom AdjoinRoot.map
  rw [AdjoinRoot.lift_mk, ← Polynomial.eval₂_map, ← AdjoinRoot.algebraMap_eq, ← aeval_def,
    AdjoinRoot.aeval_eq]

/-- `adjoinRootFracHom` agrees with the two structure maps out of `D` on constants. -/
theorem adjoinRootFracHom_of {D : Type*} [CommRing D] (K : Type*) [Field K]
    [Algebra D K] (g : Polynomial D) (b : D) :
    adjoinRootFracHom K g (AdjoinRoot.of g b)
      = algebraMap K (AdjoinRoot (Polynomial.map (algebraMap D K) g)) (algebraMap D K b) := by
  have h1 : AdjoinRoot.of g b = AdjoinRoot.mk g (Polynomial.C b) := by rw [AdjoinRoot.mk_C]
  rw [h1, adjoinRootFracHom_mk, Polynomial.map_C, AdjoinRoot.mk_C]; rfl

open Polynomial in
/-- For `g` monic and `K` a fraction field of `D`, the map `adjoinRootFracHom K g` is
injective. -/
theorem adjoinRootFracHom_injective {D : Type*} [CommRing D] (K : Type*) [Field K]
    [Algebra D K] [IsFractionRing D K] (g : Polynomial D) (hg : g.Monic) :
    Function.Injective (adjoinRootFracHom K g) := by
  have hinj : Function.Injective (algebraMap D K) := IsFractionRing.injective D K
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨q, rfl⟩ := AdjoinRoot.mk_surjective x
  rw [adjoinRootFracHom_mk, AdjoinRoot.mk_eq_zero] at hx
  rw [AdjoinRoot.mk_eq_zero]
  rwa [Polynomial.map_dvd_map (algebraMap D K) hinj hg] at hx

open Polynomial in
/-- For `g` monic over a domain `D` whose image over `K = Frac D` is irreducible,
`AdjoinRoot g` is a domain (it embeds into the field `AdjoinRoot (g.map (algebraMap D K))`). -/
theorem isDomain_adjoinRoot_of_monic {D : Type*} [CommRing D] (K : Type*) [Field K]
    [Algebra D K] [IsFractionRing D K] (g : Polynomial D) (hg : g.Monic)
    (hirr : Irreducible (Polynomial.map (algebraMap D K) g)) : IsDomain (AdjoinRoot g) := by
  have : Fact (Irreducible (Polynomial.map (algebraMap D K) g)) := ⟨hirr⟩
  exact Function.Injective.isDomain (adjoinRootFracHom K g) (adjoinRootFracHom_injective K g hg)

open Polynomial in
/-- `AdjoinRoot (g.map (algebraMap D K))` is the fraction field of `AdjoinRoot g`. -/
theorem isFractionRing_adjoinRootFrac {D : Type*} [CommRing D] [IsDomain D] (K : Type*) [Field K]
    [Algebra D K] [IsFractionRing D K] (g : Polynomial D) (hg : g.Monic)
    (hirr : Irreducible (Polynomial.map (algebraMap D K) g)) :
    letI := (adjoinRootFracHom K g).toAlgebra
    IsFractionRing (AdjoinRoot g) (AdjoinRoot (Polynomial.map (algebraMap D K) g)) := by
  have : Fact (Irreducible (Polynomial.map (algebraMap D K) g)) := ⟨hirr⟩
  have := isDomain_adjoinRoot_of_monic K g hg hirr
  let := (adjoinRootFracHom K g).toAlgebra
  have halg : ∀ z, algebraMap (AdjoinRoot g) (AdjoinRoot (Polynomial.map (algebraMap D K) g)) z
      = adjoinRootFracHom K g z := fun _ => rfl
  have hinjD : Function.Injective (algebraMap D K) := IsFractionRing.injective D K
  refine ⟨⟨?_, ?_, ?_⟩⟩
  · rintro ⟨y, hy⟩
    rw [halg, isUnit_iff_ne_zero, ne_eq, ← (adjoinRootFracHom K g).map_zero]
    intro hc
    exact nonZeroDivisors.ne_zero hy (adjoinRootFracHom_injective K g hg (by rw [hc]))
  · intro z
    obtain ⟨P, rfl⟩ := AdjoinRoot.mk_surjective z
    obtain ⟨b, hbM, hb⟩ := IsLocalization.integerNormalization_spec (nonZeroDivisors D) P
    set Q := IsLocalization.integerNormalization (nonZeroDivisors D) P
    have hyne : (AdjoinRoot.of g) b ∈ nonZeroDivisors (AdjoinRoot g) := by
      rw [mem_nonZeroDivisors_iff_ne_zero]
      intro hc
      have h0 : adjoinRootFracHom K g (AdjoinRoot.of g b) = 0 := by rw [hc, map_zero]
      rw [adjoinRootFracHom_of] at h0
      have hbK : algebraMap D K b = 0 :=
        (algebraMap K (AdjoinRoot (Polynomial.map (algebraMap D K) g))).injective
          (by rw [h0, map_zero])
      exact nonZeroDivisors.ne_zero hbM (hinjD (by rw [hbK, map_zero]))
    refine ⟨⟨AdjoinRoot.mk g Q, ⟨AdjoinRoot.of g b, hyne⟩⟩, ?_⟩
    rw [halg, halg, adjoinRootFracHom_mk, adjoinRootFracHom_of, hb, Algebra.smul_def,
      IsScalarTower.algebraMap_apply D K (Polynomial K), Polynomial.algebraMap_eq, map_mul,
      AdjoinRoot.mk_C, AdjoinRoot.algebraMap_eq, mul_comm]
  · intro x y h
    exact ⟨1, by rw [halg, halg] at h; rw [adjoinRootFracHom_injective K g hg h]⟩

open Polynomial in
/-- Transport of the `K`-algebra compatibility of `adjoinRootEquivAdjoin` along
`m = minpoly K β`. -/
theorem adjoinRootEquivAdjoin_transport_commutes {K : Type*} [Field K] {L : Type*} [Field L]
    [Algebra K L] (β : L) (hβ : IsIntegral K β) (m : Polynomial K) (hm : m = minpoly K β) (d : K) :
    (hm ▸ (IntermediateField.adjoinRootEquivAdjoin K hβ).toRingEquiv :
        AdjoinRoot m ≃+* IntermediateField.adjoin K {β}) (algebraMap K (AdjoinRoot m) d)
      = algebraMap K (IntermediateField.adjoin K {β}) d := by
  subst hm
  exact (IntermediateField.adjoinRootEquivAdjoin K hβ).commutes d

open Polynomial in
/-- The monogenic step for a fixed monic lift. If `f ∈ R[X]` is monic and its reduction over
`K = κ(p)` is the minimal polynomial of `β : L`, then for `S₁ = AdjoinRoot f` and
`φ₁ = AdjoinRoot.of f` the ideal `q₁ = pS₁` is prime and lies over `p`, and `κ(q₁)` is
`K`-isomorphic to `K⟮β⟯`.

The reduction of `f` is irreducible over `K`, so `S₁ ⧸ q₁ ≅ (R ⧸ p)[X] ⧸ (f̄)` is a domain
whose fraction field is `K[X] ⧸ (minpoly K β) ≅ K⟮β⟯`. -/
public theorem exists_residueFieldEquiv_adjoin_of_monic_lift.{u, v}
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (L : Type v) [Field L] [Algebra (ResidueFieldAtPrime R p) L]
    [Module.Finite (ResidueFieldAtPrime R p) L]
    (β : L) (f : Polynomial R) (hf : f.Monic)
    (hfm : f.map (algebraMap R (ResidueFieldAtPrime R p))
      = minpoly (ResidueFieldAtPrime R p) β) :
    ∃ (_ : (Ideal.map (AdjoinRoot.of f) p).IsPrime)
      (hpq : p = (Ideal.map (AdjoinRoot.of f) p).comap (AdjoinRoot.of f)),
      ∃ (Φ : ResidueFieldAtPrime (AdjoinRoot f) (Ideal.map (AdjoinRoot.of f) p) ≃+*
          IntermediateField.adjoin (ResidueFieldAtPrime R p) {β}),
        (Φ.toRingHom.comp (inducedResidueMap (AdjoinRoot.of f) p
            (Ideal.map (AdjoinRoot.of f) p) hpq) :
          ResidueFieldAtPrime R p →+*
            IntermediateField.adjoin (ResidueFieldAtPrime R p) {β}) =
          algebraMap (ResidueFieldAtPrime R p)
            (IntermediateField.adjoin (ResidueFieldAtPrime R p) {β}) := by
  classical
  set K := ResidueFieldAtPrime R p
  set q₁ := Ideal.map (AdjoinRoot.of f) p
  set g := Polynomial.map (Ideal.Quotient.mk p) f with hg_def
  have hgmonic : g.Monic := hf.map _
  have hm : Polynomial.map (algebraMap (R ⧸ p) K) g = minpoly K β := by
    rw [hg_def, Polynomial.map_map]
    show f.map (algebraMap R K) = _
    rw [hfm]
  have hβ : IsIntegral K β := Algebra.IsIntegral.isIntegral β
  have hirr : Irreducible (Polynomial.map (algebraMap (R ⧸ p) K) g) := by
    rw [hm]
    exact minpoly.irreducible hβ
  have hdg : IsDomain (AdjoinRoot g) := isDomain_adjoinRoot_of_monic K g hgmonic hirr
  have : IsDomain ((R ⧸ p)[X] ⧸ Ideal.span {g}) := hdg
  have eAlg := AdjoinRoot.quotEquivQuotMap f p
  have hdAR : IsDomain (AdjoinRoot f ⧸ q₁) :=
    Function.Injective.isDomain eAlg.toRingEquiv.toRingHom eAlg.toRingEquiv.injective
  have hq : q₁.IsPrime := (Ideal.Quotient.isDomain_iff_prime _).mp hdAR
  have hinj : Function.Injective (AdjoinRoot.of g) :=
    (AdjoinRoot.powerBasis' hgmonic).basis.algebraMap_injective
  have hcomm : ∀ x : R, eAlg (Ideal.Quotient.mk q₁ (AdjoinRoot.of f x))
      = AdjoinRoot.of g (Ideal.Quotient.mk p x) := fun x => by
    rw [show Ideal.Quotient.mk q₁ (AdjoinRoot.of f x) = algebraMap R (AdjoinRoot f ⧸ q₁) x from
      rfl, AlgEquiv.commutes]; rfl
  have hpq : p = q₁.comap (AdjoinRoot.of f) := by
    refine le_antisymm Ideal.le_comap_map fun x hx => ?_
    have h2 : AdjoinRoot.of g (Ideal.Quotient.mk p x) = 0 := by
      rw [← hcomm, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_comap.mp hx)]
      exact map_zero _
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hinj (h2.trans (map_zero _).symm))
  refine ⟨hq, hpq, ?_⟩
  let := (adjoinRootFracHom K g).toAlgebra
  have : IsFractionRing (AdjoinRoot g) (AdjoinRoot (Polynomial.map (algebraMap (R ⧸ p) K) g)) :=
    isFractionRing_adjoinRootFrac K g hgmonic hirr
  let e : (AdjoinRoot f ⧸ q₁) ≃+* AdjoinRoot g := eAlg.toRingEquiv
  let Φ₁ : ResidueFieldAtPrime (AdjoinRoot f) q₁
      ≃+* AdjoinRoot (Polynomial.map (algebraMap (R ⧸ p) K) g) :=
    IsFractionRing.ringEquivOfRingEquiv e
  let Φ₂ : AdjoinRoot (Polynomial.map (algebraMap (R ⧸ p) K) g)
      ≃+* IntermediateField.adjoin K {β} :=
    hm ▸ (IntermediateField.adjoinRootEquivAdjoin K hβ).toRingEquiv
  refine ⟨Φ₁.trans Φ₂, ?_⟩
  have hΦ₂ : ∀ d : K, Φ₂ (algebraMap K (AdjoinRoot (Polynomial.map (algebraMap (R ⧸ p) K) g)) d)
      = algebraMap K (IntermediateField.adjoin K {β}) d :=
    adjoinRootEquivAdjoin_transport_commutes β hβ _ hm
  have hΦ₁ : ∀ a : AdjoinRoot f ⧸ q₁,
      Φ₁ (algebraMap (AdjoinRoot f ⧸ q₁) (ResidueFieldAtPrime (AdjoinRoot f) q₁) a)
        = algebraMap (AdjoinRoot g) (AdjoinRoot (Polynomial.map (algebraMap (R ⧸ p) K) g)) (e a) :=
    fun a => IsFractionRing.ringEquivOfRingEquiv_algebraMap e a
  apply IsLocalization.ringHom_ext (nonZeroDivisors (R ⧸ p))
  refine RingHom.ext fun y => ?_
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hres : algebraMap (R ⧸ p) K (Ideal.Quotient.mk p c) = algebraMap R K c := rfl
  simp only [RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.coe_trans, Function.comp_apply]
  rw [hres, inducedResidueMap_algebraMap, hΦ₁ (Ideal.Quotient.mk q₁ (AdjoinRoot.of f c)),
    show e (Ideal.Quotient.mk q₁ (AdjoinRoot.of f c)) = AdjoinRoot.of g (Ideal.Quotient.mk p c)
      from hcomm c,
    show algebraMap (AdjoinRoot g) (AdjoinRoot (Polynomial.map (algebraMap (R ⧸ p) K) g))
        (AdjoinRoot.of g (Ideal.Quotient.mk p c))
      = adjoinRootFracHom K g (AdjoinRoot.of g (Ideal.Quotient.mk p c)) from rfl,
    adjoinRootFracHom_of]
  exact hΦ₂ _

/-- **Monogenic step.** For any `α : L` there is a finite free `φ₁ : R →+* S₁` such that
`pS₁` is prime and lies over `p`, and the induced residue field extension `κ(pS₁) / κ(p)` is
`κ(p)`-isomorphic to the simple subextension `κ(p)⟮α⟯` of `L`. -/
public theorem exists_isFiniteFree_residueField_equiv_adjoin.{u, v}
    (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
    (L : Type v) [Field L] [Algebra (ResidueFieldAtPrime R p) L]
    [Module.Finite (ResidueFieldAtPrime R p) L]
    (α : L) :
    ∃ (S₁ : Type u) (_ : CommRing S₁) (φ₁ : R →+* S₁),
      IsFiniteFree φ₁ ∧
      ∃ (_ : (Ideal.map φ₁ p).IsPrime) (hpq : p = (Ideal.map φ₁ p).comap φ₁),
        ∃ (Φ : ResidueFieldAtPrime S₁ (Ideal.map φ₁ p) ≃+*
            IntermediateField.adjoin (ResidueFieldAtPrime R p) {α}),
          (Φ.toRingHom.comp (inducedResidueMap φ₁ p (Ideal.map φ₁ p) hpq) :
            ResidueFieldAtPrime R p →+*
              IntermediateField.adjoin (ResidueFieldAtPrime R p) {α}) =
            algebraMap (ResidueFieldAtPrime R p)
              (IntermediateField.adjoin (ResidueFieldAtPrime R p) {α}) := by
  obtain ⟨β, f, hf, hadj, hfm⟩ := exists_monic_lift_minpoly R p L α
  obtain ⟨hq, hpq, Φ, hΦ⟩ := exists_residueFieldEquiv_adjoin_of_monic_lift R p L β f hf hfm
  refine ⟨AdjoinRoot f, inferInstance, AdjoinRoot.of f, isFiniteFree_adjoinRoot_of R f hf,
    hq, hpq, ?_⟩
  rw [← hadj]
  exact ⟨Φ, hΦ⟩

/-- A finite field extension of degree at least `2` has an element generating a subextension of
degree at least `2`: any `α` outside the image of `K` will do, since `K⟮α⟯` of degree `1` is `⊥`,
which contains no such `α`. -/
theorem Stacks.Flatness.FiniteFreeResidueExtension.exists_two_le_finrank_adjoin
    (K : Type*) [Field K] (L : Type*) [Field L]
    [Algebra K L] [Module.Finite K L] (h2 : 2 ≤ Module.finrank K L) :
    ∃ α : L, 2 ≤ Module.finrank K (IntermediateField.adjoin K {α}) := by
  have hne : (⊥ : Subalgebra K L) ≠ ⊤ := by
    rw [ne_eq, Subalgebra.bot_eq_top_iff_finrank_eq_one]
    omega
  obtain ⟨α, hα⟩ : ∃ α : L, α ∉ (⊥ : Subalgebra K L) :=
    not_forall.mp fun hall => hne (top_unique fun x _ => hall x)
  refine ⟨α, le_of_not_gt fun hlt => hα ?_⟩
  have h1 : Module.finrank K (IntermediateField.adjoin K {α}) = 1 :=
    le_antisymm (by omega) Module.finrank_pos
  rw [← IntermediateField.bot_toSubalgebra]
  exact IntermediateField.finrank_eq_one_iff.mp h1 ▸ IntermediateField.mem_adjoin_simple_self K α

/-- The lemma in the form the induction uses: for every degree `d`, every commutative ring `R`,
prime `p ⊆ R` and finite extension `L / κ(p)` of degree `d` satisfies `Stacks07NEConcl R p L`.

Strong induction on `d`. For `d ≤ 1` this is
  `exists_isFiniteFree_residueFieldEquiv_of_finrank_le_one`. For `d ≥ 2` take an `α ∈ L`
whose simple subextension `L' = κ(p)⟮α⟯` has degree at least `2` over `κ(p)`; realize
`L'` as the residue field `κ(pS₁)` of a finite free `φ₁ : R →+* S₁` by
  `exists_isFiniteFree_residueField_equiv_adjoin`,
transport the `L'`-algebra structure of `L` to a `κ(pS₁)`-algebra structure along that
isomorphism, and apply the induction hypothesis at `[L : L'] = [L : κ(p)] / [L' : κ(p)] < d`.
Composing the two finite free maps gives the witness for `(R, p, L)`. -/
public theorem exists_finiteFree_residueFieldEquiv_of_finrank_eq.{u, v} (d : ℕ) :
    ∀ (R : Type u) [CommRing R] (p : Ideal R) [p.IsPrime]
      (L : Type v) [Field L] [Algebra (ResidueFieldAtPrime R p) L]
      [Module.Finite (ResidueFieldAtPrime R p) L],
      Module.finrank (ResidueFieldAtPrime R p) L = d → Stacks07NEConcl R p L := by
  induction d using Nat.strong_induction_on with
  | _ d IH =>
    intro R _ p _ L _ _ _ hdim
    by_cases hle : d ≤ 1
    · exact exists_isFiniteFree_residueFieldEquiv_of_finrank_le_one R p L (by rwa [hdim])
    · push Not at hle
      set K := ResidueFieldAtPrime R p
      obtain ⟨α, hL'rank2⟩ :=
        Stacks.Flatness.FiniteFreeResidueExtension.exists_two_le_finrank_adjoin K L
          (by rw [hdim]; omega)
      obtain ⟨S₁, _, φ₁, hff₁, hq₁, hpq₁, Φ₁, hΦ₁⟩ := exists_isFiniteFree_residueField_equiv_adjoin
        R p L α
      set q₁ := Ideal.map φ₁ p
      set L' := IntermediateField.adjoin K {α}
      obtain ⟨Φc, hΦc⟩ : ∃ Φ : ResidueFieldAtPrime S₁ q₁ ≃+* L',
          Φ.toRingHom.comp (inducedResidueMap φ₁ p q₁ hpq₁) = algebraMap K L' :=
        ⟨_, hΦ₁⟩
      clear hΦ₁
      let algκq₁L' : Algebra (ResidueFieldAtPrime S₁ q₁) L' := Φc.toRingHom.toAlgebra
      let algκq₁ : Algebra (ResidueFieldAtPrime S₁ q₁) L :=
        ((algebraMap L' L).comp Φc.toRingHom).toAlgebra
      have halgmap : (algebraMap (ResidueFieldAtPrime S₁ q₁) L)
          = (algebraMap L' L).comp Φc.toRingHom := rfl
      have : IsScalarTower (ResidueFieldAtPrime S₁ q₁) L' L :=
        IsScalarTower.of_algebraMap_eq fun _ => rfl
      have : Module.Finite L' L := Module.Finite.right K L' L
      have hbijΦ₁ : Function.Bijective (algebraMap (ResidueFieldAtPrime S₁ q₁) L') :=
        Φc.bijective
      have : Module.Finite (ResidueFieldAtPrime S₁ q₁) L' :=
        Module.Finite.of_surjective
          (Algebra.linearMap (ResidueFieldAtPrime S₁ q₁) L') hbijΦ₁.surjective
      have : Module.Finite (ResidueFieldAtPrime S₁ q₁) L :=
        Module.Finite.trans L' L
      have hrankL'1 : Module.finrank (ResidueFieldAtPrime S₁ q₁) L' = 1 := by
        rw [← (AlgEquiv.ofBijective (Algebra.ofId _ L') hbijΦ₁).toLinearEquiv.finrank_eq,
          Module.finrank_self]
      have : Module.Free (ResidueFieldAtPrime S₁ q₁) L' := Module.Free.of_divisionRing _ _
      have : Module.Free L' L := Module.Free.of_divisionRing _ _
      have : Module.Free K L' := Module.Free.of_divisionRing _ _
      have hmul_new : Module.finrank (ResidueFieldAtPrime S₁ q₁) L' *
          Module.finrank L' L = Module.finrank (ResidueFieldAtPrime S₁ q₁) L :=
        Module.finrank_mul_finrank (ResidueFieldAtPrime S₁ q₁) L' L
      have hmul_old : Module.finrank K L' * Module.finrank L' L = Module.finrank K L :=
        Module.finrank_mul_finrank K L' L
      have hnewrank : Module.finrank (ResidueFieldAtPrime S₁ q₁) L = Module.finrank L' L := by
        rw [← hmul_new, hrankL'1, one_mul]
      have hdrop : Module.finrank (ResidueFieldAtPrime S₁ q₁) L < d := by
        have hbound : 2 * Module.finrank L' L ≤ d := by
          rw [← hdim, ← hmul_old]
          exact Nat.mul_le_mul_right _ hL'rank2
        have hpos : 0 < Module.finrank L' L := Module.finrank_pos
        rw [hnewrank]; omega
      obtain ⟨S, _, φ₂, hff₂, hq₂, hpq₂, Φ₂, hΦ₂⟩ :=
        IH (Module.finrank (ResidueFieldAtPrime S₁ q₁) L) hdrop S₁ q₁ L rfl
      refine ⟨S, inferInstance, φ₂.comp φ₁, isFiniteFree_comp φ₁ φ₂ hff₁ hff₂, ?_⟩
      -- The ideal must be rewritten in a `have`, not in the goal: the goal's
      -- `ResidueFieldAtPrime S (Ideal.map (φ₂.comp φ₁) p)` carries a proof argument depending on
      -- the bound primality witness, so `rw [← Ideal.map_map]` has no type-correct motive.
      have key : ∃ (_ : (Ideal.map φ₂ q₁).IsPrime)
          (hpq : p = Ideal.comap (φ₂.comp φ₁) (Ideal.map φ₂ q₁)),
          ∃ Φ : ResidueFieldAtPrime S (Ideal.map φ₂ q₁) ≃+* L,
            Φ.toRingHom.comp (inducedResidueMap (φ₂.comp φ₁) p (Ideal.map φ₂ q₁) hpq)
              = algebraMap (ResidueFieldAtPrime R p) L := by
        refine ⟨hq₂, by rw [← Ideal.comap_comap, ← hpq₂, ← hpq₁], Φ₂, ?_⟩
        rw [inducedResidueMap_comp φ₁ φ₂ p q₁ _ hpq₁ hpq₂, ← RingHom.comp_assoc, hΦ₂, halgmap,
          RingHom.comp_assoc, hΦc]
        exact (IsScalarTower.algebraMap_eq K L' L).symm
      rwa [show Ideal.map φ₂ q₁ = Ideal.map (φ₂.comp φ₁) p from Ideal.map_map φ₁ φ₂] at key

/-- Stacks Tag 07NE (Lemma 10.159.3). Given a commutative ring `R`, a prime `p`, and a finite
field extension `L / κ(p)`, there exist a commutative ring `S` and a finite free ring map
`φ : R →+* S` such that, with `q := pS = Ideal.map φ p`:
* `q` is prime;
* `q` lies over `p` (`p = q.comap φ`);
* the induced residue field extension `κ(q) / κ(p)` is `κ(p)`-isomorphic to `L / κ(p)`, i.e.
  there is a ring isomorphism `Φ : κ(q) ≃+* L` whose composite with the induced map
  `κ(p) → κ(q)` equals the structure map `κ(p) → L`. -/
@[stacks 07NE, sga "3 V 4.1.2" "finite K/k case"]
theorem exists_isFiniteFree_residueField_equiv.{u, v}
    (R : Type u) [CommRing R] (p : Ideal R) [hp : p.IsPrime]
    (L : Type v) [Field L] [Algebra (ResidueFieldAtPrime R p) L]
    [Module.Finite (ResidueFieldAtPrime R p) L] :
    ∃ (S : Type u) (_ : CommRing S) (φ : R →+* S),
      IsFiniteFree φ ∧
      ∃ (_ : (Ideal.map φ p).IsPrime) (hpq : p = (Ideal.map φ p).comap φ),
        ∃ (Φ : ResidueFieldAtPrime S (Ideal.map φ p) ≃+* L),
          (Φ.toRingHom.comp (inducedResidueMap φ p (Ideal.map φ p) hpq) :
            ResidueFieldAtPrime R p →+* L) = algebraMap (ResidueFieldAtPrime R p) L :=
  exists_finiteFree_residueFieldEquiv_of_finrank_eq
    (Module.finrank (ResidueFieldAtPrime R p) L) R p L rfl

/-! ### Realizing an arbitrary residue field extension by a flat local ring map

Good lifts of `A` towards `F` are organized into a category, in which a coherent directed system
is a functor and the colimits of `LocalConstruction.lean` are the colimits of well-ordered shapes;
adjoining one missing element of `F` is a successor structure on that category, and the transfinite
assembly is its iteration, run far enough that some stage's residue embedding is already onto.
-/

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.SmallObject

namespace GoodLift

section Assembly

variable {A : Type w} [CommRing A] [IsLocalRing A] {F : Type w} [Field F]
  [Algebra (ResidueField A) F]

/-- A morphism of good lifts: a local ring map of the carriers which extends the maximal ideal,
commutes with the structure maps and is compatible with the embeddings into `F`. Flatness is not
required of a morphism: flatness of every stage over `A` is part of `GoodLift`, and the colimit
engine needs only locality of the transition maps. -/
private structure Hom (g h : GoodLift A F) : Type w where
  /-- the underlying ring map of carriers -/
  ψ : g.carrier →+* h.carrier
  /-- the ring map is local -/
  isLocal : IsLocalHom ψ
  /-- the maximal ideal of the target is generated by the image of the maximal ideal -/
  maxeq : maximalIdeal h.carrier = Ideal.map ψ (maximalIdeal g.carrier)
  /-- the ring map commutes with the structure maps from `A` -/
  φcomp : ψ.comp g.φ = h.φ
  /-- the induced map of residue fields is compatible with the embeddings into `F` -/
  ιcomp : h.ι.comp (@ResidueField.map _ _ _ _ _ _ ψ isLocal) = g.ι

/-- Two morphisms of good lifts with the same underlying ring map are equal: all other fields
are propositions. -/
private theorem Hom.ext' {g h : GoodLift A F} {f₁ f₂ : Hom g h} (H : f₁.ψ = f₂.ψ) :
    f₁ = f₂ := by
  cases f₁; cases f₂; subst H; rfl

/-- Good lifts of `A` towards `F` form a category, with `GoodLift.Hom` for its morphisms. -/
@[instance_reducible] private def category : Category.{w} (GoodLift A F) where
  Hom g h := Hom g h
  id g :=
    { ψ := RingHom.id g.carrier
      isLocal := ⟨fun _ ha => ha⟩
      maxeq := by rw [Ideal.map_id]
      φcomp := RingHom.id_comp _
      ιcomp := by rw [IsLocalRing.ResidueField.map_id, RingHom.comp_id] }
  comp {g h l} f₁ f₂ :=
    { ψ := f₂.ψ.comp f₁.ψ
      isLocal := by
        have := f₁.isLocal; have := f₂.isLocal; exact RingHom.isLocalHom_comp _ _
      maxeq := by rw [f₂.maxeq, f₁.maxeq, Ideal.map_map]
      φcomp := by rw [RingHom.comp_assoc, f₁.φcomp, f₂.φcomp]
      ιcomp := by
        have := f₁.isLocal; have := f₂.isLocal
        rw [IsLocalRing.ResidueField.map_comp f₁.ψ f₂.ψ, ← RingHom.comp_assoc, f₂.ιcomp,
          f₁.ιcomp] }
  id_comp _ := Hom.ext' (RingHom.comp_id _)
  comp_id _ := Hom.ext' (RingHom.id_comp _)
  assoc _ _ _ := Hom.ext' (RingHom.comp_assoc _ _ _).symm

attribute [local instance] category

/-- **Recognizing a morphism of good lifts on an exhausting family.** Let `ψ` be a ring map
`g.carrier →+* h.carrier` whose composite with a family of morphisms `p i : l i ⟶ g` is the
underlying map of a family of morphisms `q i : l i ⟶ h`, and let the images of the `p i` cover
`g.carrier`. Then `ψ` is a morphism of good lifts `g ⟶ h`.

This is what makes the colimit descent one lemma: the maximal-ideal and structure-map clauses
hold already at a single index, by `Ideal.map_map` and associativity, while locality and the
compatibility with the residue embeddings are clauses about elements, so for an element coming
from the index `i` they are the corresponding clauses for `p i` and `q i`. -/
private def Hom.ofExhaustive {I : Type*} {l : I → GoodLift A F} {g h : GoodLift A F}
    (p : ∀ i, Hom (l i) g) (q : ∀ i, Hom (l i) h) (ψ : g.carrier →+* h.carrier)
    (hfac : ∀ i, ψ.comp (p i).ψ = (q i).ψ) (hexh : ∀ z : g.carrier, ∃ i x, (p i).ψ x = z)
    (i₀ : I) : Hom g h where
  ψ := ψ
  isLocal := by
    refine ⟨fun z hz => ?_⟩
    obtain ⟨i, x, rfl⟩ := hexh z
    rw [show ψ ((p i).ψ x) = (q i).ψ x from DFunLike.congr_fun (hfac i) x] at hz
    have := (q i).isLocal
    exact (isUnit_of_map_unit (q i).ψ x hz).map (p i).ψ
  maxeq := by
    calc maximalIdeal h.carrier
        = Ideal.map (q i₀).ψ (maximalIdeal (l i₀).carrier) := (q i₀).maxeq
      _ = Ideal.map (ψ.comp (p i₀).ψ) (maximalIdeal (l i₀).carrier) := by rw [hfac]
      _ = Ideal.map ψ (Ideal.map (p i₀).ψ (maximalIdeal (l i₀).carrier)) :=
          (Ideal.map_map _ _).symm
      _ = Ideal.map ψ (maximalIdeal g.carrier) := by rw [← (p i₀).maxeq]
  φcomp := by
    rw [← (p i₀).φcomp, ← RingHom.comp_assoc, hfac i₀]
    exact (q i₀).φcomp
  ιcomp := by
    refine RingHom.ext fun x => ?_
    obtain ⟨z, rfl⟩ := residue_surjective (R := g.carrier) x
    obtain ⟨i, y, rfl⟩ := hexh z
    have hp := DFunLike.congr_fun (p i).ιcomp (residue (l i).carrier y)
    have hq := DFunLike.congr_fun (q i).ιcomp (residue (l i).carrier y)
    simp only [RingHom.coe_comp, Function.comp_apply, ResidueField.map_residue] at hp hq ⊢
    rw [show ψ ((p i).ψ y) = (q i).ψ y from DFunLike.congr_fun (hfac i) y, hq, hp]

/-- A morphism of good lifts enlarges the subfield of `F` cut out by the residue embedding. -/
private theorem range_ι_subset {g h : GoodLift A F} (f : Hom g h) :
    Set.range g.ι ⊆ Set.range h.ι := by
  rintro x ⟨y, rfl⟩
  refine ⟨@ResidueField.map _ _ _ _ _ _ f.ψ f.isLocal y, ?_⟩
  simpa using DFunLike.congr_fun f.ιcomp y

/-- Isomorphic good lifts cut out the same subfield of `F`. -/
private theorem range_ι_eq_of_iso {g h : GoodLift A F} (e : g ≅ h) :
    Set.range g.ι = Set.range h.ι :=
  Set.Subset.antisymm (range_ι_subset e.hom) (range_ι_subset e.inv)

/-- **Colimits of directed systems of good lifts.** A functor from a directed nonempty preorder
to good lifts has a colimit: its carrier is the colimit ring of the carriers, by the engine
`goodLift_colimit_chosen_noflat`, and a family of morphisms out of the stages descends to it by
`GoodLift.Hom.ofExhaustive`. -/
private theorem hasColimit_of_directed {I : Type w} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] (D : I ⥤ GoodLift A F) : HasColimit D := by
  classical
  obtain ⟨i₀⟩ := ‹Nonempty I›
  obtain ⟨ub, s, hsl, hcoc, hmax, hphi, hiota, hexh, huniv⟩ :=
    goodLift_colimit_chosen_noflat (fun i => D.obj i)
      (fun i j hij => (D.map (homOfLE hij)).ψ)
      (fun i => by rw [show homOfLE (le_refl i) = 𝟙 i from rfl, D.map_id]; rfl)
      (fun i j k hij hjk => by
        rw [show homOfLE (le_trans hij hjk) = homOfLE hij ≫ homOfLE hjk from rfl, D.map_comp]
        rfl)
      (fun i j hij => (D.map (homOfLE hij)).isLocal)
      (fun i j hij => (D.map (homOfLE hij)).φcomp)
      (fun i j hij => (D.map (homOfLE hij)).ιcomp)
  let leg (i : I) : Hom (D.obj i) ub :=
    { ψ := s i, isLocal := hsl i, maxeq := hmax i, φcomp := hphi i, ιcomp := hiota i }
  let cc : Cocone D :=
    { pt := ub
      ι :=
        { app := leg
          naturality := fun i j f => Hom.ext' (by
            show (s j).comp ((D.map f).ψ) = (RingHom.id ub.carrier).comp (s i)
            rw [RingHom.id_comp]
            exact hcoc i j (leOfHom f)) } }
  have key : ∀ sc : Cocone D, ∃ m : Hom ub sc.pt, ∀ i, m.ψ.comp (s i) = (sc.ι.app i).ψ := by
    intro sc
    obtain ⟨ψ, hψ⟩ := huniv sc.pt.carrier (fun i => (sc.ι.app i).ψ)
      (fun i j hij => congrArg Hom.ψ (sc.w (homOfLE hij)))
    exact ⟨Hom.ofExhaustive leg (fun i => sc.ι.app i) ψ hψ hexh i₀, hψ⟩
  exact ⟨⟨cc,
    { desc := fun sc => (key sc).choose
      fac := fun sc i => Hom.ext' ((key sc).choose_spec i)
      uniq := fun sc m hm => Hom.ext' (RingHom.ext fun z => by
        obtain ⟨i, x, rfl⟩ := hexh z
        exact DFunLike.congr_fun
          ((congrArg Hom.ψ (hm i)).trans ((key sc).choose_spec i).symm) x) }⟩⟩

/-- Good lifts admit the colimits needed to iterate a successor structure over a well-ordered
type: colimits of the shapes `Set.Iio j` for a successor limit `j`, and of the shape `J`. -/
private theorem hasIterationOfShape (J : Type w) [LinearOrder J] [OrderBot J] :
    HasIterationOfShape J (GoodLift A F) := by
  have : Nonempty J := ⟨⊥⟩
  constructor
  · intro j hj
    have : Nonempty (Set.Iio j) := ⟨⟨_, (not_isMin_iff.mp hj.not_isMin).choose_spec⟩⟩
    exact ⟨fun D => hasColimit_of_directed D⟩
  · exact ⟨fun D => hasColimit_of_directed D⟩

/-- **One monogenic step, as a successor.** Every good lift admits a morphism to a good lift
which, unless its residue embedding was already onto `F`, cuts out a strictly larger subfield of
`F`: adjoin an element of `F` outside the range (`goodLift_monogenic_step`). -/
private theorem exists_step (g : GoodLift A F) :
    ∃ (h : GoodLift A F) (_ : Hom g h),
      ¬ Function.Surjective g.ι → Set.range g.ι ⊂ Set.range h.ι := by
  classical
  by_cases hs : Function.Surjective g.ι
  · exact ⟨g, 𝟙 g, fun h => absurd hs h⟩
  · obtain ⟨α, hα⟩ : ∃ α : F, α ∉ Set.range g.ι :=
      (Set.ne_univ_iff_exists_notMem _).1 fun he => hs (Set.range_eq_univ.1 he)
    obtain ⟨h, m, hm, -, mmax, mφ, mι, hcov⟩ := goodLift_monogenic_step g α
    let f : Hom g h := { ψ := m, isLocal := hm, maxeq := mmax, φcomp := mφ, ιcomp := mι }
    exact ⟨h, f, fun _ => (Set.ssubset_iff_of_subset (range_ι_subset f)).2 ⟨α, hcov, hα⟩⟩

/-- The successor structure on good lifts: adjoin one missing element of `F` at each step,
starting from `A` itself. -/
private noncomputable def succStruct : SuccStruct (GoodLift A F) where
  X₀ := goodLift_trivial A F
  succ g := (exists_step g).choose
  toSucc g := (exists_step g).choose_spec.choose

/-- **The transfinite assembly.** For a local ring `A` and a field extension `F` of its residue
field there is a good lift of `A` towards `F` whose residue embedding is onto `F`, i.e. a flat
local `A`-algebra `A'` with `𝔪_{A'} = 𝔪_A A'` and residue field `F`.

This is the content of Stacks 03C3: starting from `goodLift_trivial` one adjoins the elements
of `F` one at a time by `exists_step` (i.e. `goodLift_monogenic_step`), taking the colimits of
`hasColimit_of_directed` at limit stages; the tower is the iteration of `succStruct` over an
index type longer than `Set F`, so some stage's residue embedding is already onto. -/
@[ega "0 10.3.1.4" "terminal ring B=A_γ", sga "3 V 4.1.2"]
private theorem exists_surjective_ι :
    ∃ g : GoodLift A F, Function.Surjective g.ι := by
  classical
  by_contra hcon
  simp only [not_exists] at hcon
  set κ : Cardinal.{w} := Order.succ (2 ^ Cardinal.mk F)
  have hne : Nonempty κ.ord.ToType := by
    rw [Ordinal.nonempty_toType_iff]
    simpa [Cardinal.ord_eq_zero] using (lt_of_le_of_lt zero_le (Order.lt_succ _)).ne'
  let : OrderBot κ.ord.ToType := WellFoundedLT.toOrderBot κ.ord.ToType
  have := hasIterationOfShape (A := A) (F := F) κ.ord.ToType
  set Φ := succStruct (A := A) (F := F)
  have hmono : StrictMono fun j => Set.range ((Φ.iterationFunctor κ.ord.ToType).obj j).ι := by
    intro j j' hjj'
    have hlt : Set.range ((Φ.iterationFunctor κ.ord.ToType).obj j).ι
        ⊂ Set.range ((Φ.iterationFunctor κ.ord.ToType).obj (Order.succ j)).ι := by
      rw [range_ι_eq_of_iso (Φ.iterationFunctorObjSuccIso j (not_isMax_iff.mpr ⟨j', hjj'⟩))]
      exact (exists_step _).choose_spec.choose_spec (hcon _)
    exact lt_of_lt_of_le hlt (range_ι_subset
      ((Φ.iterationFunctor κ.ord.ToType).map (homOfLE (Order.succ_le_of_lt hjj'))))
  have h1 : Cardinal.mk κ.ord.ToType ≤ Cardinal.mk (Set F) :=
    Cardinal.mk_le_of_injective hmono.injective
  rw [Cardinal.mk_ord_toType, Cardinal.mk_set] at h1
  exact absurd h1 (not_le.mpr (Order.lt_succ _))

end Assembly

end GoodLift

/-- **A residue field extension is realized by a flat local ring map**, in one universe and in
ring-map form: for a local ring `A` and a ring map `kmap : ResidueField A →+* F` into a field
there is a flat local `A`-algebra `A'` with `𝔪_{A'} = 𝔪_A A'` whose residue field is
`F`-isomorphic over `kmap`. -/
@[ega "0 10.3.1" "partial", ega "III 4.3.4" "partial"]
private theorem exists_flat_of_residueFieldHom (A : Type w) [CommRing A] [IsLocalRing A]
    (F : Type w) [Field F] (kmap : ResidueField A →+* F) :
    ∃ (A' : Type w) (_ : CommRing A') (_ : IsLocalRing A') (φ : A →+* A') (hφ : IsLocalHom φ),
      φ.Flat ∧ maximalIdeal A' = Ideal.map φ (maximalIdeal A) ∧
      ∃ σ : ResidueField A' ≃+* F,
        (σ : ResidueField A' →+* F).comp (@ResidueField.map A A' _ _ _ _ φ hφ) = kmap := by
  let : Algebra (ResidueField A) F := kmap.toAlgebra
  obtain ⟨g, hsurj⟩ := GoodLift.exists_surjective_ι (A := A) (F := F)
  exact ⟨g.carrier, g.commRing, g.isLocalRing, g.φ, g.hφ, g.flat, g.maxeq,
    RingEquiv.ofBijective g.ι ⟨g.ι.injective, hsurj⟩,
    g.hι.trans (RingHom.algebraMap_toAlgebra kmap)⟩

/-- The residue field map of a ring isomorphism of local rings cancels that of its inverse. -/
private theorem residueField_map_comp_map_symm {A B : Type*} [CommRing A] [IsLocalRing A]
    [CommRing B] [IsLocalRing B] (e : A ≃+* B) :
    (ResidueField.map (e : A →+* B)).comp (ResidueField.map (e.symm : B →+* A))
      = RingHom.id (ResidueField B) := by
  refine RingHom.ext fun x => ?_
  obtain ⟨y, rfl⟩ := residue_surjective (R := B) x
  simp [ResidueField.map_residue]

/-- **The same across universes.** `exists_flat_of_residueFieldHom` for a local ring `A` and a
field `F` in independent universes, the algebra `A'` landing in `Type (max u v)`: run the
construction over `ULift.{v} A` and `ULift.{u} F` and transport the conclusion back along
`ULift.ringEquiv`, flatness by `RingHom.Flat.comp_iff_of_bijective_right`, the maximal ideal by
`IsLocalRing.map_ringEquiv_maximalIdeal` and the residue embedding by the cancellation
`residueField_map_comp_map_symm`. -/
@[ega "0 10.3.1" "partial", sga "3 V 4.1.2"]
private theorem exists_flat_of_residueFieldHom' (A : Type u) [CommRing A] [IsLocalRing A]
    (F : Type v) [Field F] (kmap : ResidueField A →+* F) :
    ∃ (A' : Type max u v) (_ : CommRing A') (_ : IsLocalRing A') (φ : A →+* A')
      (hφ : IsLocalHom φ),
      φ.Flat ∧ maximalIdeal A' = Ideal.map φ (maximalIdeal A) ∧
      ∃ σ : ResidueField A' ≃+* F,
        (σ : ResidueField A' →+* F).comp (@ResidueField.map A A' _ _ _ _ φ hφ) = kmap := by
  let e : ULift.{v} A ≃+* A := ULift.ringEquiv
  let f : ULift.{u} F ≃+* F := ULift.ringEquiv
  have : IsLocalRing (ULift.{v} A) := e.symm.isLocalRing
  obtain ⟨A', cA', lA', φ, hφ, hflat, hmax, σ, hσ⟩ :=
    exists_flat_of_residueFieldHom (ULift.{v} A) (ULift.{u} F)
      ((f.symm : F →+* ULift.{u} F).comp
        (kmap.comp (ResidueField.map (e : ULift.{v} A →+* A))))
  have := hφ
  refine ⟨A', cA', lA', φ.comp (e.symm : A →+* ULift.{v} A), inferInstance,
    (RingHom.Flat.comp_iff_of_bijective_right e.symm.bijective).2 hflat, ?_, σ.trans f, ?_⟩
  · rw [← Ideal.map_map, show Ideal.map (e.symm : A →+* ULift.{v} A) (maximalIdeal A)
      = maximalIdeal (ULift.{v} A) from map_ringEquiv_maximalIdeal e.symm]
    exact hmax
  · refine RingHom.ext fun x => ?_
    have h := DFunLike.congr_fun hσ (ResidueField.map (e.symm : A →+* ULift.{v} A) x)
    have hc := DFunLike.congr_fun (residueField_map_comp_map_symm e) x
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply,
      RingEquiv.coe_toRingHom] at h hc
    simp only [RingEquiv.coe_trans, RingHom.coe_comp, Function.comp_apply, RingEquiv.coe_toRingHom,
      ResidueField.map_comp, h, RingEquiv.apply_symm_apply, hc]

/-- **A residue field extension is realized by a flat local ring map** (Stacks 03C3). Let
`(R, 𝔪, k)` be a local ring and let `K` be a field extension of `k`. Then there is a local ring
`(R', 𝔪', k')` and a local ring map `R → R'` such that `R'` is flat over `R`, `𝔪' = 𝔪 R'`, and
`k'` is isomorphic to `K` as an extension of `k`. -/
@[stacks 03C3 "The lemma's preamble, a local ring `R'` and a local ring map `R → R'`, is the
`Algebra R R'`, `IsLocalRing R'` and `IsLocalHom (algebraMap R R')` binders; the conjuncts are
flatness, `𝔪' = 𝔪 R'` as `Ideal.map`, and `k' ≅ K` as an extension of `k` as an
`≃ₐ[ResidueField R]`. `K` is allowed to live in a universe of its own, the source's case being
`v = u`. See the module docstring.",
  sga "3 V 4.1.2" "first assertion",
  ega "0 10.3.1" "flat local ext, k'≅K", ega "III 4.3.4" "partial"]
theorem IsLocalRing.exists_flat_residueField_algEquiv (R : Type u) [CommRing R]
    [IsLocalRing R] (K : Type v) [Field K] [Algebra (ResidueField R) K] :
    ∃ (R' : Type (max u v)) (_ : CommRing R') (_ : Algebra R R') (_ : IsLocalRing R')
      (_ : IsLocalHom (algebraMap R R')),
      Module.Flat R R' ∧
      (maximalIdeal R).map (algebraMap R R') = maximalIdeal R' ∧
      Nonempty (ResidueField R' ≃ₐ[ResidueField R] K) := by
  obtain ⟨R', cR', lR', φ, hφ, hflat, hmax, σ, hσ⟩ :=
    exists_flat_of_residueFieldHom' R K (algebraMap (ResidueField R) K)
  have := hφ
  let : Algebra R R' := φ.toAlgebra
  have hAM : algebraMap R R' = φ := RingHom.algebraMap_toAlgebra φ
  have hlh : IsLocalHom (algebraMap R R') := hAM ▸ hφ
  refine ⟨R', cR', ‹Algebra R R'›, lR', hlh, ?_, by rw [hAM, hmax],
    ⟨AlgEquiv.ofRingEquiv (f := σ) fun x => ?_⟩⟩
  · exact hflat
  · exact DFunLike.congr_fun hσ x

end
