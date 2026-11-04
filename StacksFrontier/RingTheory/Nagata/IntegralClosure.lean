module

import StacksCore.FieldTheory.AlgebraicClosure
import StacksFrontier.RingTheory.Flat.ReducedFibres
public import StacksFrontier.RingTheory.Nagata.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

universe u v

/-!
# Finiteness of the integral closure of a Nagata ring in a reduced algebra

Proof of `IsIntegralClosure.finite_of_essFiniteType_of_isReduced`: for a Nagata ring `R` — a
Noetherian ring all of whose prime quotients `R ⧸ p` are N-2 (Japanese) — and a reduced
`R`-algebra `S` essentially of finite type, the integral closure of `R` in `S` is a finite
`R`-module.

The argument is the source's. Being essentially of finite type over a Noetherian ring, `S` is
Noetherian, so it has finitely many minimal primes `q`; being reduced, it embeds into the product
of the residue fields `κ(q) = Frac(S ⧸ q)`, each of which is again essentially of finite type
over `R`. Over `R` Noetherian it therefore suffices to bound the integral closure of `R` in a
single field `K` essentially of finite type over `R`. There `p = ker(R → K)` is prime, the
integral closures of `R` and of the domain `R ⧸ p` in `K` have the same elements, and `K` is a
finitely generated field extension of `κ(p) = Frac(R ⧸ p)`. The relative algebraic closure `L` of
`κ(p)` in `K` is then finite over `κ(p)` (Tag 037J), every element of `K` integral over `R` lies
in `L`, and the N-2 hypothesis at `p` bounds the integral closure of `R ⧸ p` in `L`.

## Main results

* `Stacks.Nagata.IntegralClosureFinite.solution`: the proof of
  `IsIntegralClosure.finite_of_essFiniteType_of_isReduced`.

## Implementation notes

The two transfer steps of the argument are isolated as
`Stacks.Nagata.IntegralClosureFinite.surjective_mapIntegralClosure` (change of the ambient ring
along a map absorbing all integral elements) and
`Stacks.Nagata.IntegralClosureFinite.finite_integralClosure_of_finite_tower` (change of the base
ring along a finite extension inside the ambient ring); neither mentions fields, and both are the
shape in which the source uses them.

The reduction of the general `A` with `IsIntegralClosure A R S` to the concrete subalgebra
`integralClosure R S` is `IsIntegralClosure.equiv`, as in the sibling `IsIntegralClosure.finite`.

The source writes the embedding of the reduced ring `S` into the product of its localizations at
the minimal primes (Tags 02LX, 00EU). Here `S ⧸ q` is used in place of `S_q`: for `q` minimal the
two have the same fraction field, and `Frac(S ⧸ q)` is a field with no reducedness argument
needed, while injectivity of `S → ∏ Frac(S ⧸ q)` is the statement that the minimal primes
intersect in the nilradical.

## References

* [Stacks Project, Tag 03GH](https://stacks.math.columbia.edu/tag/03GH)
-/

namespace Stacks.Nagata.IntegralClosureFinite


/-- A reduced ring embeds into the product, over its minimal primes `q`, of the fraction fields
of the domains `S ⧸ q`: an element killed by every one of these maps is zero. -/
private theorem eq_zero_of_forall_algebraMap_fractionRing_eq_zero {S : Type*} [CommRing S]
    [IsReduced S] {s : S} (h : ∀ q ∈ minimalPrimes S,
      algebraMap (S ⧸ q) (FractionRing (S ⧸ q)) (Ideal.Quotient.mk q s) = 0) : s = 0 :=
  Stacks.Flatness.ReducedFibreAscent.eq_zero_of_forall_mem_minimalPrimes fun q hq =>
    Ideal.Quotient.eq_zero_iff_mem.mp
      ((map_eq_zero_iff _ (IsFractionRing.injective (S ⧸ q) (FractionRing (S ⧸ q)))).mp (h q hq))

/-- An injective `R`-algebra map `f : A →ₐ[R] B` whose range contains every element of `B`
integral over `R` carries the integral closure of `R` in `A` *onto* the integral closure of `R`
in `B`. -/
private theorem surjective_mapIntegralClosure {R A B : Type*} [CommRing R] [CommRing A]
    [CommRing B] [Algebra R A] [Algebra R B] (f : A →ₐ[R] B) (hf : Function.Injective f)
    (hrange : ∀ b : B, IsIntegral R b → b ∈ Set.range f) :
    Function.Surjective f.mapIntegralClosure := by
  rintro ⟨b, hb⟩
  obtain ⟨a, rfl⟩ := hrange b hb
  exact ⟨⟨a, (isIntegral_algHom_iff f hf).mp hb⟩, Subtype.ext rfl⟩

/-- Finiteness of integral closures descends along a finite extension of the base: if `A` is a
finite `R`-algebra sitting inside `B` and the integral closure of `A` in `B` is a finite
`A`-module, then the integral closure of `R` in `B` is a finite `R`-module.

The integral closure of `R` in `B` is contained in that of `A`, which is finite over `R` by
transitivity; the containment is enough because `R` is Noetherian. -/
private theorem finite_integralClosure_of_finite_tower {R A B : Type*} [CommRing R]
    [IsNoetherianRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra A B]
    [IsScalarTower R A B] [Module.Finite R A] (h : Module.Finite A (integralClosure A B)) :
    Module.Finite R (integralClosure R B) := by
  have : Module.Finite R ↥(integralClosure A B) := Module.Finite.trans A _
  let ι : ↥(integralClosure R B) →ₗ[R] ↥(integralClosure A B) :=
    { toFun := fun x => ⟨x, x.2.tower_top⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact Module.Finite.of_injective ι fun _ _ hab =>
    Subtype.ext (congrArg (fun z : ↥(integralClosure A B) => (z : B)) hab)

/-- The integral closure of an N-2 domain `R` in a field `K` essentially of finite type over `R`
and containing `R` is a finite `R`-module.

Every element of `K` integral over `R` is algebraic over `Frac(R)`, hence lies in the relative
algebraic closure `L` of `Frac(R)` in `K`, which is a finite extension of `Frac(R)` by Tag 037J;
so the N-2 hypothesis applies to `L`. -/
private theorem finite_integralClosure_of_isJapaneseRing {R : Type u} [CommRing R] [IsDomain R]
    (hR : IsJapaneseRing R) {K : Type u} [Field K] [Algebra R K] [Algebra.EssFiniteType R K]
    (hinj : Function.Injective (algebraMap R K)) :
    Module.Finite R (integralClosure R K) := by
  let _ : Algebra (FractionRing R) K := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower R (FractionRing R) K :=
    IsScalarTower.of_algebraMap_eq fun x => (IsFractionRing.lift_algebraMap hinj x).symm
  have : Algebra.EssFiniteType (FractionRing R) K := Algebra.EssFiniteType.of_comp R _ K
  have := hR.finite (algebraicClosure (FractionRing R) K)
  let φ := (IntermediateField.val (algebraicClosure (FractionRing R) K)).restrictScalars R
  exact Module.Finite.of_surjective φ.mapIntegralClosure.toLinearMap
    (surjective_mapIntegralClosure φ Subtype.val_injective fun y hy =>
      ⟨⟨y, mem_algebraicClosure_iff.mpr (hy.tower_top (A := FractionRing R)).isAlgebraic⟩, rfl⟩)

/-- The integral closure of a Nagata ring `R` in a field `K` essentially of finite type over `R`
is a finite `R`-module.

The kernel `p` of `R → K` is prime, and `K` is essentially of finite type over the domain
`R ⧸ p`, which embeds into `K` and is N-2 by hypothesis; `R ⧸ p` is a finite `R`-module, so the
previous two lemmas apply in turn. -/
private theorem finite_integralClosure_field {R : Type u} [CommRing R] [IsNoetherianRing R]
    (hR : ∀ (p : Ideal R) [p.IsPrime], IsJapaneseRing (R ⧸ p))
    {K : Type u} [Field K] [Algebra R K] [Algebra.EssFiniteType R K] :
    Module.Finite R (integralClosure R K) := by
  have : (RingHom.ker (algebraMap R K)).IsPrime := RingHom.ker_isPrime _
  set p := RingHom.ker (algebraMap R K)
  let _ : Algebra (R ⧸ p) K := (RingHom.kerLift (algebraMap R K)).toAlgebra
  have : IsScalarTower R (R ⧸ p) K :=
    IsScalarTower.of_algebraMap_eq fun x => (RingHom.kerLift_mk (algebraMap R K) x).symm
  have : Algebra.EssFiniteType (R ⧸ p) K := Algebra.EssFiniteType.of_comp R _ K
  exact finite_integralClosure_of_finite_tower
    (finite_integralClosure_of_isJapaneseRing (hR p) (RingHom.kerLift_injective (algebraMap R K)))

/-- A reduced ring with finitely many minimal primes embeds into the product of the fraction
fields of its quotients `S ⧸ q` by them, so its integral closure over a Noetherian base `R` is
finite as soon as each of theirs is. -/
private theorem finite_integralClosure_of_forall_minimalPrimes {R S : Type*} [CommRing R]
    [IsNoetherianRing R] [CommRing S] [Algebra R S] [IsReduced S] [Finite (minimalPrimes S)]
    (h : ∀ q : minimalPrimes S,
      Module.Finite R (integralClosure R (FractionRing (S ⧸ (q : Ideal S))))) :
    Module.Finite R (integralClosure R S) := by
  let ψ : ∀ q : minimalPrimes S, S →ₐ[R] FractionRing (S ⧸ (q : Ideal S)) := fun q =>
    (IsScalarTower.toAlgHom R (S ⧸ (q : Ideal S)) _).comp (Ideal.Quotient.mkₐ R _)
  have : Module.Finite R
      (∀ q : minimalPrimes S, ↥(integralClosure R (FractionRing (S ⧸ (q : Ideal S))))) :=
    Module.Finite.pi (h := h)
  refine Module.Finite.of_injective
    (LinearMap.pi fun q => (ψ q).mapIntegralClosure.toLinearMap) fun a b hab => ?_
  refine Subtype.ext (sub_eq_zero.mp
    (eq_zero_of_forall_algebraMap_fractionRing_eq_zero fun q hq => ?_))
  simpa [ψ, sub_eq_zero, Subtype.ext_iff] using congrFun hab ⟨q, hq⟩

/-- **A Nagata ring has finite integral closure in a reduced algebra essentially of finite type.**

Let `R` be a Nagata ring, that is, a Noetherian ring such that `R ⧸ p` is N-2 (Japanese) for
every prime `p`, and let `S` be a reduced `R`-algebra essentially of finite type. Then the
integral closure `A` of `R` in `S` is a finite `R`-module. -/
@[ega "II 6.3.10" "special case"]
public theorem solution
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] [IsReduced S]
    {A : Type v} [CommRing A] [Algebra R A] [Algebra A S] [IsScalarTower R A S]
    [IsIntegralClosure A R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime], IsJapaneseRing (R ⧸ p)) :
    Module.Finite R A := by
  have : IsNoetherianRing S := Algebra.EssFiniteType.isNoetherianRing R S
  have : Finite (minimalPrimes S) := (minimalPrimes.finite_of_isNoetherianRing S).to_subtype
  -- a local instance, so that each `Frac(S ⧸ q)` below is a field
  have : ∀ q : minimalPrimes S, (q : Ideal S).IsPrime :=
    fun q => (Minimal.prop (Set.mem_ofPred.mp q.2)).1
  have : Module.Finite R (integralClosure R S) :=
    finite_integralClosure_of_forall_minimalPrimes fun _ => finite_integralClosure_field hR
  exact Module.Finite.equiv
    (IsIntegralClosure.equiv R A S (integralClosure R S)).symm.toLinearEquiv

end Stacks.Nagata.IntegralClosureFinite

/-!
# Finiteness of the integral closure of a Nagata ring in a reduced algebra

A Noetherian ring `R` is a **Nagata ring** when `R ⧸ p` is N-2 (Japanese) for every prime `p`
of `R`: the integral closure of `R ⧸ p` in every finite extension of its fraction field is a
finite module. This is a finiteness condition on `R` alone, yet it propagates to every algebra
essentially of finite type over `R`, and the present lemma is the first step of that propagation.

Let `R → S` be essentially of finite type, i.e. `S` is a localization of a finite type
`R`-algebra, and let `S` be reduced. Then the integral closure `A` of `R` in `S` is a finite
`R`-module. The mechanism: `S` is Noetherian with finitely many minimal primes `q₁, …, q_m` and,
being reduced, embeds into `∏ S_{qᵢ}`, each `S_{qᵢ} = κ(qᵢ)` a field which is a finitely
generated field extension of `κ(pᵢ)`, where `pᵢ` is the contraction of `qᵢ`. The algebraic closure
`Lᵢ` of `κ(pᵢ)` in `κ(qᵢ)` is therefore a *finite* extension of `κ(pᵢ)`, so the Nagata condition
at `pᵢ` bounds the integral closure of `R ⧸ pᵢ` in `Lᵢ`; that closure is the integral closure of
`R` in `κ(qᵢ)`, and `A` sits inside the product of these finitely many finite modules over the
Noetherian ring `R`.

Note that no domain hypothesis is placed on `S`, and no integrally closed hypothesis on `R`:
the two Mathlib siblings `IsIntegralClosure.finite` and `IsIntegralClosure.isNoetherian` cover
the complementary situation of a finite separable extension of the fraction field of a Noetherian
integrally closed domain, where the finiteness comes from a trace form rather than from a
condition on the base.

## Main results

* `IsIntegralClosure.finite_of_essFiniteType_of_isReduced`: the integral closure of a Nagata ring
  `R` in a reduced `R`-algebra essentially of finite type is a finite `R`-module.

## Implementation notes

The Nagata hypothesis is spelled out as its two clauses — `[IsNoetherianRing R]` together with
`IsJapaneseRing (R ⧸ p)` for every prime `p` — rather than as the single predicate `IsNagataRing`
of Tag 032R(2), so that the Noetherian clause is an instance binder and a caller holding only the
two facts need not package them; `IsJapaneseRing` is the N-2 condition of Tag 032F. The two
clauses are exactly the conjuncts of `IsNagataRing R`, both are used, and neither implies the
other, so this is the source's hypothesis verbatim and not a weakening.

The integral closure is presented abstractly, as a ring `A` with `IsIntegralClosure A R S`, rather
than as the subalgebra `integralClosure R S`; the subalgebra is an instance of the class, so the
concrete form follows by specialization, while any ring built as the integral closure of `R` in
`S` — a subring of `S`, a quotient of a polynomial ring, the normalization of a scheme — is
covered without an intervening isomorphism. This follows the sibling `IsIntegralClosure.finite`.

`S` is taken in the universe of `R`. The N-2 condition of Tag 032F quantifies over extensions in
the universe of the domain, and the extensions the proof feeds it are the residue fields of `S`;
so the alignment is what makes the imported hypothesis applicable to `S`, not a restriction of
the mathematics (a ring in another universe is isomorphic to one here, and both `Module.Finite`
and `IsIntegralClosure` transport along ring isomorphisms). The integral closure `A` is left in
an arbitrary universe.

Faithfulness. (1) Every hypothesis is live: `IsNoetherianRing R` bounds the submodule `A` of the
product of the finitely many `Aᵢ'`, the Japanese hypothesis on the quotients is what bounds each
`Aᵢ'`, `Algebra.EssFiniteType R S` gives both the Noetherianity of `S` and the finite generation
of `κ(qᵢ)` over `κ(pᵢ)`, and `IsReduced S` is what embeds `S` into the product of its residue
fields at minimal primes — dropping it makes the conclusion false already for `R = k` a field and
`S = k[x, y]/(y²)`, where every element of `y · k[x]` is nilpotent, hence integral over `k`, so
that the integral closure of `k` in `S` is infinite dimensional over `k`. (2) The
scalars and base are the source's: finiteness is asserted of `A` as a module over `R` itself, and
the Japanese condition is imposed on the quotients `R ⧸ p` of `R`, not on localizations of `S`.
(3) The source's canonical object "the integral closure `A` of `R` in `S`" is pinned by
`IsIntegralClosure A R S` — `A` is integral over `R`, maps injectively to `S`, and its image is
exactly the set of elements of `S` integral over `R` — with `IsScalarTower R A S` fixing the
factorization `R → A → S` of the structure map. (4) The instantiation is not degenerate: `R = ℤ`
with `S = ℚ` gives `A = ℤ`, and `R = k` a field with `S = k(x)` gives `A = k`, both instances in
which the conclusion holds nonvacuously while `S` is neither finite nor integral over `R`.

## References

* [Stacks Project, Tag 03GH](https://stacks.math.columbia.edu/tag/03GH)
-/

@[expose] public section



/-- **A Nagata ring has finite integral closure in a reduced algebra essentially of finite type.**

Let `R` be a Nagata ring, that is, a Noetherian ring such that `R ⧸ p` is N-2 (Japanese) for
every prime `p`, and let `S` be a reduced `R`-algebra essentially of finite type. Then the
integral closure `A` of `R` in `S` is a finite `R`-module. -/
@[stacks 03GH, ega "II 6.3.10" "special case"]
public theorem IsIntegralClosure.finite_of_essFiniteType_of_isReduced
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {S : Type u} [CommRing S] [Algebra R S] [Algebra.EssFiniteType R S] [IsReduced S]
    {A : Type v} [CommRing A] [Algebra R A] [Algebra A S] [IsScalarTower R A S]
    [IsIntegralClosure A R S]
    (hR : ∀ (p : Ideal R) [p.IsPrime], IsJapaneseRing (R ⧸ p)) :
    Module.Finite R A :=
  Stacks.Nagata.IntegralClosureFinite.solution (S := S) hR

end
